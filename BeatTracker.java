/**
 * An effective beat tracker using dynamic programming
 * Yuan Gao, 2011
 */
import processing.core.*; 
import processing.xml.*; 

import ddf.minim.analysis.*; 
import ddf.minim.*; 

import java.applet.*; 
import java.awt.Dimension; 
import java.awt.Frame; 
import java.awt.event.MouseEvent; 
import java.awt.event.KeyEvent; 
import java.awt.event.FocusEvent; 
import java.awt.Image; 
import java.io.*; 
import java.net.*; 
import java.text.*; 
import java.util.*; 
import java.util.zip.*;
import java.util.regex.*; 

public class BeatTracker extends PApplet
{
    Minim minim;
    AudioPlayer sound;
    AudioSnippet blip;
    FFT fft;

    int bufferSize = 512; // fft size

    /* log-frequency averaging controls */
    int minBW = 50; // minimum bandwidth
    int binsPerOct = 4; // bins per octave
    int nBand; // number of bands

    float gThresh = 0.1f; // mouse-controlled threshold

    /* delay line to synchronize blips */
    int blipDelayLen = 16;
    int[] blipDelay = new int[blipDelayLen];

    int sinceLast = 0; // counter to suppress double-beats

    float framePeriod;

    /* storage space */
    int colmax = 300;
    float[] onsets = new float[colmax];
    float[] scorefun = new float[colmax];
    float[] dobeat = new float[colmax];
    int now = 0; // time index for circular buffer within above

    float[] spec; // the spectrum of the previous step

    boolean paused = false;

    /* Autocorrelation structure */
    int maxlag = 100; // (in frames) largest lag to track
    float decay = 0.997f; // smoothing constant for running average
    Autoco auco;

    float alph = 100 * gThresh; // trade-off constant between tempo deviation penalty and onset strength

    public void setup()
    {
        size(300, 250, P2D);
        textMode(SCREEN);

        minim = new Minim(this);
        sound = minim.loadFile("aphextwin.wav", bufferSize);
        sound.play();

        /* load a short blip, added at the beat times */
        blip = minim.loadSnippet("blip.wav");

        fft = new FFT(sound.bufferSize(), sound.sampleRate());
        fft.window(FFT.HAMMING);
        fft.logAverages(minBW, binsPerOct);

        nBand = fft.avgSize();
        // println("Number of bins: " + nBand);

        framePeriod = /*2 * */sound.bufferSize() / sound.sampleRate();
        frameRate(1 / framePeriod);
        // println("Target frame period: " + round(1000 * framePeriod) + " ms");  

        // initialize record of previous spectrum
        spec = new float[nBand];
        for (int i = 0; i < nBand; ++i) spec[i] = -100.0f;

        auco = new Autoco(maxlag, decay, framePeriod);
    }

    // utility function to plot a vector of floats in a rectangle
    public void plotVec(int x, int y, int w, int h, 
                        float[] vec, int vecLen, int stt, 
                        int joined, int r, int g, int b) 
    {
        // find the largest value and scale everything by that
        float maxVal = 0;
        for (int i = 0; i < vecLen; ++i)
            if (vec[i] > maxVal)
                maxVal = vec[i];

        noFill();
        stroke(r, g, b);
        int yy = y + h - (int)(h * (vec[0] / maxVal));
        int lastX = x;
        for (int i = 0; i < vecLen; ++i) {
            int yo = yy;
            yy = y + h - (int)(h * (vec[(stt + i) % vecLen] / maxVal));
            int nextX = x + ((i * w) / vecLen);
            if (joined == 1) 
                line(lastX, yo, nextX, yy);
            else
                line(nextX, y + h, nextX, yy);  
            lastX = nextX;
        }
        // add legend as the actual peak value
        text(maxVal, x, y + 10);
    }

    public void draw()
    {
        if (!paused) {
            fft.forward(sound.mix);

            /* calculate the value of the onset function in this frame */
            float onset = 0;
            for(int i = 0; i < nBand; i++) {
                float specVal = (float) max(-100.0f, 20.0f * (float)Math.log10(fft.getAvg(i))); // dB value of this band
                float dbInc = specVal - spec[i]; // dB increment since last frame
                spec[i] = specVal; // record this frome to use next time around
                onset += dbInc; // onset function is the sum of dB increments
            }
            onset = onset / 400; // scale it to keep it in a sensible range
            onsets[now] = onset;

            /* update autocorrelator and find peak lag = current tempo */
            auco.newVal(onset);
            // record largest value in (weighted) autocorrelation as it will be the tempo
            float aMax = 0.0f;
            int tempopd = 0;
            float[] acVals = new float[maxlag];
            for(int i = 0; i < maxlag; ++i) {
                float acVal = (float) sqrt(auco.autoco(i));
                if (acVal > aMax) {
                    aMax = acVal;
                    tempopd = i;
                }
                // store in array backwards, so it displays right-to-left, in line with traces
                acVals[maxlag - 1 - i] = acVal;
            }

            /* calculate DP-ish function to update the best-score function */
            float smax = -999999;
            int smaxix = 0;
            // weight can be varied dynamically with the mouse
            alph = 100 * gThresh;
            // consider all possible preceding beat times from 0.5 to 2.0 x current tempo period
            for(int i = tempopd / 2; i < min(colmax, 2 * tempopd); ++i) {
                // objective function - this beat's cost + score to last beat + transition penalty
                float score = onset + scorefun[(now - i + colmax) % colmax] - alph * (float)pow(log((float)i / (float)tempopd), 2);
                // keep track of the best-scoring predecesor
                if (score > smax) {
                    smax = score;
                    smaxix = i;
                }
            }
            scorefun[now] = smax;
            // keep the smallest value in the score fn window as zero, by subtracing the min val
            float smin = scorefun[0];
            for(int i = 0; i < colmax; ++i)
                if (scorefun[i] < smin)
                    smin = scorefun[i];
            for(int i = 0; i < colmax; ++i)
                scorefun[i] -= smin;

            /* find the largest value in the score fn window, to decide if we emit a blip */
            smax = scorefun[0];
            smaxix = 0;
            for(int i = 0; i < colmax; ++i) {
                if (scorefun[i] > smax) {
                    smax = scorefun[i];
                    smaxix = i;
                }
            }
            // dobeat array records where we actally place beats
            dobeat[now] = 0;  // default is no beat this frame
            ++sinceLast;
            // if current value is largest in the array, probably means we're on a beat
            if (smaxix == now) {
                // make sure the most recent beat wasn't too recently
                if (sinceLast > tempopd / 4) {
                    // setting blipDelay[0] schedules a blip to be played in sync
                    blipDelay[0] = 1;
                    // record that we did actually mark a beat this frame
                    dobeat[now] = 1;
                    // reset counter of frames since last beat
                    sinceLast = 0;
                }
            }

            background(0);
            noFill();
            /* plot the onset strength function in white */
            plotVec(0, 0, colmax, height / 8, onsets, colmax, now, 1, 255, 255, 255);
            /* plot the running autocorrelation values in royal blue */
            plotVec(colmax - maxlag, height / 4, maxlag, height / 8, acVals, maxlag, 0, 0, 128, 128, 255);
            /* Indicate the peak autoco val in red */
            stroke(255, 128, 128);
            line(colmax - tempopd, height / 4, colmax - tempopd, height / 4 + height / 8);
            /* plot the best score function in green */
            plotVec(0, height / 2, colmax, height / 8, scorefun, colmax, now, 1, 128, 255, 128);
            /* plot the record of when beats (blips) are declared in purple */
            plotVec(0, 3 * height / 4, colmax, height / 8, dobeat, colmax, now, 0, 255, 128, 255);

            /* show the line corresponding to mouse-controlled threshold */
            stroke(128);
            line(0, (int)(height * (1 - gThresh)), colmax, (int)(height * (1 - gThresh)));

            fill(255);
            text(round(60 / (tempopd * framePeriod)) + " bpm", 10, height - 5);

            /* update column index (for ring buffer) */
            if(++now == colmax) now = 0;

            /* short delay line to synchronize blips with main playback */
            for (int i = blipDelayLen - 1; i > 0; --i) blipDelay[i] = blipDelay[i-1];
            blipDelay[0] = 0;
            /* empirically, this is how long we need to delay to make blips sound right */
            if (blipDelay[5] == 1) {
                blip.rewind();
                blip.play();
            }
        }
    }

    public void keyPressed()
    {
        if (key == ' ') {
            paused = !paused;
            if (paused) {
                sound.pause();
            } else {
                sound.play();
            }
        }
    }

    public void mousePressed()
    {
        // mouse press up/down adjusts weight to balance onsets & history
        gThresh = ((float)(height - mouseY)) / (float)height;
    }

    public void mouseDragged()
    {
        mousePressed();
    }

    public void stop()
    {
        sound.close();
        minim.stop(); 
        super.stop();
    }

    // class to compute an array of online autocorrelators
    private class Autoco
    {
        private int del_length;
        private float decay;
        private float[] delays;
        private float[] outputs;
        private int indx;

        private float[] bpms;
        private float[] rweight;
        private float wmidbpm = 120.0f;
        private float woctavewidth = 2.0f;

        public Autoco(int len, float alpha, float framePeriod)
        {
            decay = alpha;
            del_length = len;
            delays = new float[del_length];
            outputs = new float[del_length];
            indx = 0;

            // calculate a log-lag gaussian weighting function, to prefer tempi around 120 bpm
            bpms = new float[del_length];
            rweight = new float[del_length];
            for (int i = 0; i < del_length; ++i) {
                bpms[i] = 60.0f / (framePeriod * (float)i);
                // weighting is Gaussian on log-BPM axis, centered at wmidbpm, SD = woctavewidth octaves
                rweight[i] = (float)exp(-0.5f * pow(log(bpms[i] / wmidbpm) / log(2.0f) / woctavewidth, 2.0f));
            }
        }

        public void newVal (float val)
        {
            delays[indx] = val;

            // update running autocorrelator values
            for (int i = 0; i < del_length; ++i) {
                int delix = (indx - i + del_length) % del_length;
                outputs[i] += (1 - decay) * (delays[indx] * delays[delix] - outputs[i]);
            }
            if (++indx == del_length) indx = 0;
        }

        // read back the current autocorrelator value at a particular lag
        public float autoco(int del)
        {
            return rweight[del] * outputs[del];
        }
    }

    static public void main(String args[]) {
        PApplet.main(new String[] { "--bgcolor=#FFFFFF", "BeatTracker" });
    }
}
