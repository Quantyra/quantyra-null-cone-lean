"""
    Set input data by modifying the config.json file.
NOTE: in the name of the section, the ".txt" extension need not be specified. It is assumed

Config entry keys:
    - "plot": boolean, if true will plot the data for this measurement
    - "label" str, label to place on legend
    - "laser_rate": float, repetition rate of laser in Hz
    - "color": str, color to plot data in
    - "tau_dead_default": float, value of tau_dead in ns
    - "tau_dead_path": str, path to data for dead time vs flux (no .txt extension) OVERWRITES VALUE OF tau_dead
        Assumed format: one column with countrate (Hz) and second column with dead time (ns).
        We take upper and lower bounds from this value

Three sections:

    First section: set-up
        - Subplots are prepared for showing final fit
        - To plot for both tau_on-off and tau_continuous, tau_on-off is kept fixed,
        and the fit repeated for several values of tau_on-off (tau_dead)
        - The script loads data with the following format:
            count rate,detection efficiency,standard uncertainty
        - The name of the data is specified in the first section,
        and all is stored in the dictionary 'data'. This dictionary has keys explained in
        the first entry below.
        - Data rearranged as needed

    Second section: fits

In these fits, the on-off time is determined experimentally and hard-coded in the data
dictionary defined in the first section. From this, the continuous recovery time is determined
"""
import json
import logging
import matplotlib as mpl
import matplotlib.pyplot as plt
import numpy as np

from experiment_analytical import get_qeff_sps, sigmoid_recovery, Data, RECOVERY_THRESHOLD
from lib_fits import analyze_data

mpl.use('Qt5Agg')
plt.rcParams.update({'font.size': 30})
mpl.rc('axes', linewidth=2)

PLOT_ABSOLUTE = True
recovery_fun = sigmoid_recovery
SUM_ORDER = 5000


def load_data():
    """
    Loads data and prepares subplots
    :return: 
    """
    with open("config.json", "r") as fp:
        data_all = json.load(fp)  # also contains data not to be plotted
    data = {}
    for key in data_all:
        if data_all[key]["plot"]:
            data[key] = data_all[key]

    # preparing logs and plots
    logger = logging.getLogger()
    logger.setLevel(logging.INFO)
    plt.close("all")
    _, (ax_snspd, ax_SPAD) = plt.subplots(1, 2, sharex="all",
                                          figsize=(17, 9.5))

    # properly loading data
    for txt in data:
        vals = np.loadtxt(f"{txt}.txt",
                          delimiter=",", skiprows=1)
        # measured counts divided by net efficiency
        data[txt]["counts"] = vals[:, 0]
        data[txt]["q_eff"] = vals[:, 1] * (1 - data[txt]["afterpulsing"])
        data[txt]["flux"] = data[txt]["counts"] / data[txt]["q_eff"]
        data[txt]["1_sig"] = vals[:, 2]
        data[txt]["axis"] = ax_snspd if "snspd" in txt else ax_SPAD  # axs[i]

        if data[txt].get("tau_dead_path"):
            dead_time_vals = np.loadtxt(f"{txt}_dead_time.txt",
                                        delimiter=",", skiprows=1)
            data[txt]["tau_dead_bounds"] = [min(dead_time_vals[:, 1]) * 1e-9,
                                            max(dead_time_vals[:, 1]) * 1e-9]
            data[txt]["tau_dead"] = np.mean(data[txt]["tau_dead_bounds"])
        else:
            data[txt]["tau_dead"] = data[txt]["tau_dead_default"] * 1e-9
            data[txt]["tau_dead_bounds"] = [data[txt]["tau_dead"], data[txt]["tau_dead"]]
    return data


def fit_data(data):
    for fit_key in data:
        # defining the fit function
        res2, r2 = analyze_data(data[fit_key], recovery_fun)
        data[fit_key]["fit_params"] = res2
        txt = (f'Fit for {data[fit_key]["label"]}:\t'
               f't_dead:{data[fit_key]["tau_dead"] / 1e-9:.1f}ns\t'
               f't_rst:{data[fit_key]["fit_params"][1] / 1e-9:.1f}ns\t'
               f'eta_0:{data[fit_key]["fit_params"][0]:.3f}\t'
               f'R^2: {round(r2, 2)}.')
        with open("count_fig.log", "a") as fp:
            fp.write(txt)
        print(txt)

        data[fit_key]["params"] = Data(
            tau_dead=data[fit_key]["tau_dead"],
            tau_rst=data[fit_key]["fit_params"][1],
            eta=data[fit_key]["fit_params"][0],
            recovery_fn=recovery_fun,
            f=data[fit_key]["laser_rate"],
            recovery_threshold=RECOVERY_THRESHOLD
        )
    return data


def plot_data(data, normalize):
    """
    
    :param data: 
    :param normalize: normalize efficiency 
    :return: 
    """
    # if data.get("snspd1"):  # force the snspd values from the time_definitions values
    #     data["snspd1"]["params"].eta = 0.87
    #     data["snspd1"]["params"].tau_dead = 19.29e-9
    #     data["snspd1"]["params"].tau_rst = 6.76e-9

    for fit_key in data:
        # backdoor to force parameters
        data[fit_key]["params"].eta = data[fit_key].get("forced_eta",
                                                        data[fit_key]["params"].eta)
        data[fit_key]["params"].tau_dead = data[fit_key].get("forced_t_dead",
                                                             data[fit_key]["params"].tau_dead * 1e9) / 1e9
        data[fit_key]["params"].tau_rst = data[fit_key].get("forced_t_rst",
                                                            data[fit_key]["params"].tau_rst * 1e9) / 1e9


        def prepare_label(params: Data):
            label = data[fit_key]["label"]
            # label += "\n"
            # label += r"$\eta_0$=%.3f" % params.eta + "\n"
            # label += r"$\tau_{rst}$=%.1f" % (params.tau_rst * 1e9)
            return label

        y_norm = get_qeff_sps(0, params=data[fit_key]["params"]) if normalize else 1
        x_fit = np.logspace(0,
                            np.log10(max(data[fit_key]["flux"])),
                            num=200)
        y_fit = get_qeff_sps(x_fit,
                             params=data[fit_key]["params"],
                             ) / y_norm
        # saving data
        fit_params: Data = data[fit_key]["params"]
        with open(f"{fit_key}_fit.txt", "w") as fp:
            fp.write(
                f"metadata:\ttau_dead={fit_params.tau_dead:.2e}\t"
                f"tau_rst={fit_params.tau_rst:.2e}\neta_0={fit_params.eta:.3f}\n")
            fp.write("flux,detection efficiency\n")
            for count, eff in zip(x_fit, y_fit):
                fp.write(f'{count:.4f},{eff:.4f}\n')

        y_fit_bounds = [
            get_qeff_sps(x_fit,
                         params=data[fit_key]["params"]) / y_norm for t in data[fit_key]["tau_dead_bounds"]]
        # plot fits
        data[fit_key]["axis"].plot(x_fit / 1e6,
                                   y_fit,
                                   "-",
                                   label=prepare_label(data[fit_key]["params"]),
                                   c=data[fit_key]["color"])
        data[fit_key]["axis"].fill_between(
            x=x_fit / 1e6,
            y1=y_fit_bounds[0],
            y2=y_fit_bounds[1],
            color=data[fit_key]["color"],
            alpha=0.5
        )

        # plot data
        data[fit_key]["axis"].errorbar(data[fit_key]["flux"] / 1e6,
                                       data[fit_key]["q_eff"] / y_norm,
                                       yerr=data[fit_key]["1_sig"] * 2,
                                       fmt="o",
                                       c=data[fit_key]["color"])
        # data[fit_key]["axis"].set_title('[' + data[fit_key]["label"] + ']' +
        #                                 r" $\tau_{dead}$ = %.1f" % (data[fit_key]['params'].tau_dead * 1e9))

    # making nicer graphs
    for fit_key in data:
        data[fit_key]["axis"].grid(visible=True, which="both")
        data[fit_key]["axis"].set_xlabel(r"Photon flux ($10^6$ s$^{-1}$)")
        data[fit_key]["axis"].legend(loc="lower left")
        data[fit_key]["axis"].set_xlim(left=0)
        data[fit_key]["axis"].set_ylabel(r"$\langle\eta_{eff}\rangle$")  # make sure to label all axes

    # plt.suptitle("Recovery: " + recovery_fun.__name__)
    plt.tight_layout()
    plt.savefig("figure_3_bc.svg")
    plt.show()

    # plotting and saving recovery shape
    for key in data:
        plt.figure()
        tau_dead = data[key]["params"].tau_dead
        tau_rcv = data[key]["params"].tau_rcv
        times = np.linspace(0, tau_dead + tau_rcv * 3, num=100)
        # recovery = (1 - recovery_fun(-(times - tau_dead) / tau_rcv) )* rect(times - tau_dead)
        recovery = recovery_fun(times, params=data[key]["params"], )

        plt.vlines(tau_dead * 1e9, ymin=0, ymax=1, colors="black", linestyles="dashed",
                   label=r"$\tau_{dead}$")
        plt.vlines((tau_dead + tau_rcv) * 1e9, ymin=0, ymax=1, colors="red", linestyles="dashed",
                   label=r"$\tau_{rcv}$")
        plt.arrow(x=tau_dead * 1e9, y=0.8,
                  dx=tau_rcv * 1e9, dy=0,
                  width=0.01,
                  head_width=0.05, head_length=2,
                  length_includes_head=True,
                  color="black")
        plt.legend()
        plt.plot(times * 1e9, recovery)
        plt.title(f"Recovery for {key}.")
        plt.xlabel("Time (ns)")
        plt.ylabel("Recovery")
        plt.tight_layout()
        plt.savefig(f"recovery_{key}.png")


if __name__ == '__main__':
    DATA = fit_data(load_data())
    plot_data(DATA, normalize=not PLOT_ABSOLUTE)
