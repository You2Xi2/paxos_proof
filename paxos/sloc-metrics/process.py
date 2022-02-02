import sys
import os
import csv
import datetime
import matplotlib.pyplot as plt
from matplotlib.backends.backend_pdf import PdfPages

PROTOCOL_FILES = {'agents.dfy', 'network.dfy', 'synod.dfy', 'types.dfy'}
PROOF_FILES = {'proof.dfy', 'proof_agreement.dfy', 'proof_agreement_invariants.dfy', 'proof_helper.dfy', 'proof_validity.dfy', 'proof_agreement_chosenProperties1.dfy', 'proof_agreement_chosenProperties2.dfy', 'proof_axioms.dfy', 'proof_agreement_chosenProperties.dfy'}


def main(sloc_dir):

    # Parse data
    data = dict()  # map from dafny timestamp -> filename -> lines of code)
    for root, _, files in os.walk(sloc_dir):
        csv_files = [f for f in files if f[-4:] == ".csv"]  # process only csv files
        process_files(csv_files, data)

    # Plot graphs
    visualize_data(data)


"""
Adds to data dictionary the information from each file in csv_files
"""
def process_files(csv_files, data):
    for csvf in csv_files:
        with open(csvf, 'r') as f:
            timestr = csvf[:-4]
            timestamp = datetime.datetime.strptime(timestr, '%y-%d-%b-%H%M')
            data[timestamp] = dict()

            csvreader = csv.reader(f, delimiter=',',)
            next(csvreader)  # skip header row

            for row in csvreader:
                dafnyf = row[0].strip()
                lines = int(row[1].strip())

                data[timestamp][dafnyf] = lines


def visualize_data(data):
    x_vals = sorted(list(data.keys()))
    
    # Prepare y values
    y_protocol = [get_protocol_lines(data, t) for t in x_vals]
    y_proof = [get_proof_lines(data, t) for t in x_vals]

    with PdfPages("graph.pdf") as pp:
        fig, ax = plt.subplots(1, 1, figsize=(8.5, 11), sharex=True)
        fig.suptitle("Lines of Code", fontsize=12, fontweight='bold')
        ax.grid()
        ax.plot(x_vals, y_protocol, label='protocol', color='navy')
        ax.plot(x_vals, y_proof, label='proof', color='firebrick')
        
        fig.tight_layout()
        fig.subplots_adjust(bottom=0.2)

        ax.set_xticklabels(x_vals, rotation = 45)
        plt.legend()
        pp.savefig(fig)
        plt.close(fig)
        
    


def get_protocol_lines(data, timestamp):
    res = 0
    for f in PROTOCOL_FILES:
        res += data[timestamp][f]
    return res

def get_proof_lines(data, timestamp):
    res = 0
    for f in PROOF_FILES:
        if f in data[timestamp]:
            res += data[timestamp][f]
    return res


if __name__ == "__main__":
    # positional arguments <sloc_dir>
    sloc_dir = sys.argv[1]
    main(sloc_dir)