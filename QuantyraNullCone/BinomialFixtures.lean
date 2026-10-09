import QuantyraNullCone.BinomialArithmetic

namespace QuantyraNullCone

/-- Zero events give the complete interval. -/
theorem binomial_zero_sample_fixture :
    binomialReportCheck 0 (1/20) (fun _ => 0) (fun _ => 1) = true := by
  simp [binomialReportCheck, binomial_no_data_valid]

/-- A small exact report, independently reduced by the kernel. -/
theorem binomial_one_sample_fixture :
    binomialReportCheck 1 (1/20)
      (fun k => if k = 0 then 0 else 1/64)
      (fun k => if k = 0 then 63/64 else 1) = true := by
  norm_num [binomialReportCheck, BinomialReportValid, binomialUpperTailQ,
    binomialLowerTailQ, binomialMassQ, Fin.forall_fin_succ, Fin.sum_univ_succ]

theorem binomial_bad_report_rejected :
    binomialReportCheck 1 (1/20) (fun _ => 1/2) (fun _ => 1/2) = false := by
  norm_num [binomialReportCheck, BinomialReportValid, binomialUpperTailQ,
    binomialLowerTailQ, binomialMassQ, Fin.forall_fin_succ, Fin.sum_univ_succ]

theorem binomial_reversed_report_rejected :
    binomialReportCheck 0 (1/20) (fun _ => 1) (fun _ => 0) = false := by
  norm_num [binomialReportCheck, BinomialReportValid, Fin.forall_fin_succ]

end QuantyraNullCone
