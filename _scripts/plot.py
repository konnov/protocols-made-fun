#!/usr/bin/env python3

import matplotlib.pyplot as plt
import matplotlib.cbook as cbook
import matplotlib as lib
import numpy as np
from matplotlib.backends.backend_pdf import PdfPages
from matplotlib.ticker import FuncFormatter 

def plot_times():
    fig = plt.figure()
    data = np.genfromtxt('prng2-times.csv', dtype=None, delimiter=',', names=True)

    plt.rcParams.update({'font.size': 11})
    plt.rcParams.update({'font.size': 11})

    plt.plot(data['nsamples'], data['safety'], 'bs', fillstyle='none',
             label='safety', markersize=10, linestyle='--')
    plt.plot(data['nsamples'], data['missingOutput'], 'ro', fillstyle='none',
             label='missingOutput', markersize=10, linestyle='--')
    plt.xlabel('Number of samples, --max-samples')
    plt.ylabel('Running times (sec.)')
    #plt.semilogy()
    #plt.ylim([0, 10])
    #plt.xlim([0, 40])
    plt.grid(True, alpha=.2)
    # https://matplotlib.org/stable/api/legend_api.html
    # lower right
    plt.legend(loc=4)
    #plt.tick_params(axis='x', rotation=-25)
    plt.tight_layout()
    # Format x-axis labels as plain numbers
    plt.gca().xaxis.set_major_formatter(FuncFormatter(lambda x, _: format(int(x), ',')))

    plt.savefig('prng2-times.png', dpi=300)

    #with PdfPages('prng2-times.pdf') as pdf:
    #    pdf.savefig(fig)

    plt.clf()

if __name__ == "__main__":
    plot_times()
