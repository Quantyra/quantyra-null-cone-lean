import numpy as np
from typing import Any, Callable
from scipy.optimize import curve_fit

from experiment_analytical import get_qeff_sps


def analyze_data(data_dict: dict[str, Any], recovery_fun: Callable):
    """
    data_dict must contain entries:
        - flux: list of float
        - q_eff: list of float
        - 1_sig: list of float (errors on q_eff)
        -laser_rate: MHz, float
        -tau_dead: float or list of float
    """
    from experiment_analytical import Data

    def sps_curve_fit(x, eta,
                      tau_rst
                      ):
        params = Data(
            tau_dead=data_dict["tau_dead"],
            tau_rst=tau_rst,
            recovery_fn=recovery_fun,
            eta=eta,
            f=data_dict["laser_rate"]
        )
        return get_qeff_sps(x,
                            params,
                            )

    def get_r2_sps(x, y, eta,
                   tau_rst
                   ):
        """
        function for getting r-squared error
        """
        params = Data(
            tau_dead=data_dict["tau_dead"],
            tau_rst=tau_rst,
            recovery_fn=recovery_fun,
            eta=eta,
            f=data_dict["laser_rate"]
        )
        fit = get_qeff_sps(x,
                           params,
                           )

        n = len(x)
        return 1.0 - sum((y - fit) ** 2) / ((n - 1.0) * np.var(y, ddof=1))

    # set guess parameter for efficiency and fit
    eta_guess = max(data_dict["q_eff"])
    eta_bounds = [eta_guess, 1.05 * eta_guess]  # the measured value is a lower bound
    tau_rst_guess = data_dict["tau_dead"]
    tau_bounds = [0, 50e-9]
    res2, cov2, infodict2, msg2, ier2 = curve_fit(sps_curve_fit,
                                                  data_dict["flux"],
                                                  data_dict["q_eff"],
                                                  p0=np.array([eta_guess, tau_rst_guess]),
                                                  sigma=data_dict["1_sig"],
                                                  bounds=([eta_bounds[0], tau_bounds[0]],
                                                          [eta_bounds[1], tau_bounds[1]]),
                                                  full_output=True)

    assert ier2 in [1, 2, 3, 4], "curve fit failed"
    r2 = get_r2_sps(data_dict["flux"], data_dict["q_eff"],
                    res2[0],
                    res2[1]
                    )

    return res2, r2
