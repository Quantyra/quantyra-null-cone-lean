from dataclasses import dataclass
from typing import Callable

import matplotlib.pyplot as plt
import numpy as np
from scipy.optimize import fsolve

plt.rcParams.update({'font.size': 18})

RECOVERY_EXPONENT = 4
RECOVERY_THRESHOLD = 0.95


@dataclass
class Data:
    tau_dead: float or iter
    tau_rst: float or iter
    recovery_fn: Callable | None = None
    f: float | None = None
    eta: float | None = None
    recovery_threshold: float = RECOVERY_THRESHOLD

    @property
    def tau_rcv(self):
        return self.tau_dead + self.tau_rst


def get_readiness(b, params, r_thresh=0.999):
    """
    Assumes the sigmoid recovery and non-paralyzable mechanics.
    """

    def root_fun(x):
        # x is readiness <R>

        b_tilde = b * params.eta
        i = 0  # np.floor(params.tau_dead * params.f)  # we can ignore all terms with smaller index cause recovery is 0
        summed_proba = 0
        total = 0

        while True:
            r = sigmoid_recovery((i + 1) / params.f, params)
            if r < r_thresh:  # don't truncate yet
                proba = b_tilde * x * (1 - b_tilde * x) ** i
                total += r * proba
                summed_proba += proba
            else:
                remaining_p = 1 - summed_proba
                total += remaining_p
                return x - total
            i += 1

    return fsolve(root_fun, np.array([0.5]), factor=0.1)[0]


def get_readinesses(b_list: iter, params: Data) -> np.ndarray:
    results = []
    for b in b_list:
        results.append(get_readiness(b, params))
    return np.array(results)


def rect(x: np.ndarray or float):
    return np.where(x >= 0, 1, 0)


def sigmoid_recovery(t: float or np.ndarray, params: Data):
    """
    Weibull "stretched exponential" function to start at zero. It's a "stretched exponential"
    """
    lam = (-np.log(1 - RECOVERY_THRESHOLD)) ** (-1/RECOVERY_EXPONENT)  # exponent to define tau_rst
    return (1 - np.exp(-((t - params.tau_dead) / lam / params.tau_rst) ** RECOVERY_EXPONENT)) * rect(t - params.tau_dead)


def get_qeff_sps(c, params: Data):
    """
    General function for getting the effective quantum efficiency. The model applied here is:
        - threshold detector
        - single-photon source input

    :param c: input counts
    :param params: Data dataclass
    """

    # defining useful terms
    b = c / params.f
    try:
        _ = iter(b)  # just checking b is iterable
        return params.eta * get_readinesses(b, params)
    except TypeError:
        return params.eta * get_readiness(b, params)


if __name__ == "__main__":
    SUM_ORDER = 2000
    data = Data(
        f=80e6,
        tau_dead=20e-9,
        tau_rst=20e-9,
        eta=0.5,
        recovery_fn=sigmoid_recovery)

    plt.close('all')

    plt.figure()
    times = np.linspace(-20, 80, num=100) * 1e-9
    plt.plot(times, sigmoid_recovery(times, data))
    plt.title("Recovery shape")
    plt.tight_layout()
    plt.show()

    plt.figure()
    bs = np.linspace(0, 1)
    plt.plot(bs, get_readinesses(bs, data))
    plt.xlabel("Brightness")
    plt.title("Readiness")
    plt.tight_layout()
    plt.show()

    plt.figure()
    counts = np.linspace(0, 20e6)
    plt.plot(counts,
             get_qeff_sps(
                 c=counts,
                 params=data,
             ))
    # plt.ylim(0, 0.51)
    plt.title("Qeff")
    plt.xlabel("Count")
    plt.show()
