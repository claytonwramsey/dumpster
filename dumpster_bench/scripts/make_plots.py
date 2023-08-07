import matplotlib.pyplot as plt
import sys

csv_file = open(sys.argv[1])

times = {}

for line in csv_file.read().split('\n'):
    if len(line) == 0:
        continue
    name, test_type, n_threads, n_ops, time = line.split(',')
    if 'shredder' in name or 'single' in test_type:
        continue
    if name not in times.keys():
        times[name] = ([], [])
    times[name][0].append(int(n_threads))
    times[name][1].append(float(time))

print(times)
for (name, v) in times.items():
    (xs, ys) = v
    plt.scatter(xs, ys, label=name)
plt.xlabel('Number of threads')
plt.ylabel('Time taken for 1Mops (ms)')
plt.title('Garbage collector shootout')
plt.legend()
plt.show()