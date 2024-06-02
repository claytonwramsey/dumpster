# dumpster, a cycle-tracking garbage collector for Rust.
# Copyright (C) 2023 Clayton Ramsey.

# This Source Code Form is subject to the terms of the Mozilla Public
# License, v. 2.0. If a copy of the MPL was not distributed with this
# file, You can obtain one at http://mozilla.org/MPL/2.0/.

import matplotlib.pyplot as plt
import sys

csv_file = open(sys.argv[1])

multi_times = {}
single_times = {}

for line in csv_file.read().split('\n'):
    if len(line) == 0:
        continue
    name, test_type, n_threads, n_ops, time = line.split(',')
    times = single_times if test_type == 'single_threaded' else multi_times
    if name not in times.keys():
        times[name] = ([], [])
    times[name][0].append(int(n_threads))
    times[name][1].append(float(time) / 1000.0)

for (name, v) in multi_times.items():
    (xs, ys) = v
    plt.scatter(xs, ys, label=name)
plt.xlabel('Number of threads')
plt.ylabel('Time taken for 1M ops (ms)')
plt.title('Parallel garbage collector scaling')
plt.legend()
plt.show()

multi_times.pop('shredder', None)
for (i, (name, v)) in enumerate(multi_times.items()):
    (xs, ys) = v
    plt.scatter(xs, ys, label=name, color=f"tab:{['blue', 'orange', 'red'][i]}")
plt.xlabel('Number of threads')
plt.ylabel('Time taken for 1M ops (ms)')
plt.title('Parallel garbage collector scaling (sans shredder)')
plt.legend()
plt.show()

def violin(times: dict, name: str):
    data = []
    labels = []
    for (label, (_, ys)) in times.items():
        data.append(ys)
        labels.append(label)

    fig = plt.figure()
    plt.violinplot(data, range(len(data)), vert=False)
    plt.yticks(range(len(data)), labels=labels)
    plt.ylabel('Garbage collector')
    plt.xlabel('Runtime for 1M ops (ms)')
    plt.tight_layout(rect=(10, 1.08, 1.08, 1.08))
    plt.title(name)
    plt.show()

violin(single_times, 'Single-threaded GC comparison')
single_times.pop('shredder', None)
violin(single_times, 'Single-threaded GC comparison (sans shredder)')
