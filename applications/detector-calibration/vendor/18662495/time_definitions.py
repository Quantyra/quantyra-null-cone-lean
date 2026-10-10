import matplotlib as mpl
import numpy as np
from matplotlib import pyplot as plt
from scipy.signal import savgol_filter

from experiment_analytical import sigmoid_recovery, Data, RECOVERY_THRESHOLD

mpl.use('Qt5Agg')
plt.rcParams.update({'font.size': 30})
mpl.rc('axes', linewidth=2)
DEAD_START = 10
"""Where to start the plot"""

# region load data
raw_data = np.loadtxt("1,3M_hist.txt", skiprows=1)
raw_times = raw_data[1:, 0] / 1e3  # converting to ns
raw_counts = raw_data[1:, 1]
smooth_counts = savgol_filter(raw_counts, 100, 3)
filter_max_counts = 60 < raw_times
max_recovery = np.mean(smooth_counts[filter_max_counts])
# endregion

# region plot for debug
# plt.figure(figsize=(9, 9.5))
# plt.plot(raw_times, raw_counts)
# plt.plot(raw_times, smooth_counts)
# plt.show()
# endregion

# region find characteristic times
blob_end = 10
raw_counts[raw_times <= blob_end] = 0

filter_dead = raw_counts <= 0.001 * max_recovery
# dead_start = raw_times[filter_dead][0]
# t_dead = raw_times[filter_dead][-1] - dead_start
t_dead = raw_times[filter_dead][-1]

filter_partial_rst = smooth_counts <= RECOVERY_THRESHOLD * max_recovery
t_reset = raw_times[filter_partial_rst][-1] - raw_times[filter_dead][-1]
params = Data(tau_dead=t_dead, tau_rst=t_reset)
# endregion

# region plot data
plot_times = raw_times
print(DEAD_START)
plt.figure(figsize=(9, 9.5))
# plt.plot(plot_times - dead_start - blob_end,
plt.plot(plot_times,
         raw_counts / max_recovery,
         label="Raw data", c="xkcd:black")
plt.plot(plot_times,
# plt.plot(plot_times - dead_start - blob_end,
         smooth_counts / max_recovery,
         label="smoothed", c="xkcd:peach", linewidth=1.5)
x_fit = plot_times[raw_times > DEAD_START]
y_fit = sigmoid_recovery(plot_times[raw_times > DEAD_START], params)
# plt.plot(x_fit - blob_end, y_fit,
plt.plot(x_fit, y_fit,
         label="fit", c="xkcd:tomato", linewidth=3)

# start of dead times
# plt.vlines(dead_start, ymin=0, ymax=2 * max_recovery, colors='black')
# end
# plt.vlines(t_dead - blob_end, 0, 2, colors="black")
plt.vlines(t_dead, 0, 2, colors="black")
# plt.vlines(t_dead + t_reset - blob_end, 0, 2, linestyles='dashed', colors="blue")
plt.vlines(t_dead + t_reset, 0, 2, linestyles='dashed', colors="blue")
# plt.vlines(dead_start + t_reset_90pct + t_dead + plot_times[0], 0, 2 * max_recovery, linestyles='dashed')

# plt.hlines(max_recovery, 0, max(raw_times), linestyles='dashed')
# plt.xlim([-dead_start, 55])
plt.xlim([DEAD_START, 55])
plt.ylim(bottom=0, top=1.6)
plt.xlabel("Time (ns)")
plt.ylabel("Normalized coincidences")
plt.grid()
# plt.legend()
plt.tight_layout()
plt.savefig("figure_3_a.svg")
print(f"t_dead: {t_dead:.2f} ns\n"
      f"t_rst ({RECOVERY_THRESHOLD * 100:.2f} pct): {t_reset:.2f} ns\n"
      )

with open("1,3M_hist_fit.txt", "w") as fp:
    fp.write(f"tau_dead: {t_dead:.2f} ns\ttau_rst: {t_reset:.2f} ns\n")
    fp.write("time(ns),counts(a.u.)\n")
    for time, recov in zip(x_fit, y_fit):
        fp.write(f'{time:.4f},{recov:.4f}\n')

plt.show()
# endregion
