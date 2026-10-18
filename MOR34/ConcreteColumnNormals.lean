import MOR34.FiniteDeterminant
import MOR34.ColumnNormalBounds

namespace MOR34

/-- Cramer normals evaluated using the verified finite recursive determinant. -/
def concreteColumnNormal {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (c : Fin r ↪ Fin d) (j k : Fin d) : ℤ :=
  (if k = j then laplaceDet r (M.submatrix id c) else 0) -
    ∑ i : Fin r, if c i = k then
      laplaceDet r ((M.submatrix id c).updateCol i (fun a => M a j)) else 0

theorem concreteColumnNormal_eq {r d : ℕ} (M : Matrix (Fin r) (Fin d) ℤ)
    (c : Fin r ↪ Fin d) : concreteColumnNormal M c = columnNormal M c := by
  funext j k
  simp only [concreteColumnNormal, columnNormal, laplaceDet_correct, Matrix.cramer_apply]

end MOR34
