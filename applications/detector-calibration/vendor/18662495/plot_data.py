import numpy as np
import matplotlib.pyplot as plt


plt.close("all")
plt.figure()
for filename in ["spad1.txt", "spad2.txt", "spad3.txt"]:
    data = np.loadtxt(rf"{filename}", skiprows=1, delimiter=",")
    counts = data[:, 0] / data[:, 1]
    eff = data[:, 1]
    eff_stf = data[:, 2]

    plt.plot(counts, eff, 'o', label=filename.replace(".txt", ""))

plt.xlabel("Flux (MHz)")
plt.ylabel("q_eff")
plt.tight_layout()
plt.legend()
plt.show()
