module

public import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.Chains.SimplexSubsetOrder

/-! # 元の部分集合 bead の端点付き連結語
概要：同じ標準単体の部分集合 bead を、共有端点と自由次元を保って連結する。
方針：元の昇順部分集合と元の左右端点を型の添字に保持する。
規約：各 bead は二点以上、次元は濃度から二を引く。使われ方：HA の全生成元値。
-/
@[expose] public section
namespace SerrePositivity.KST.SConstruction
end SerrePositivity.KST.SConstruction
namespace SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics
open _root_.SerrePositivity.KST.SConstruction

/-- 元の端点と自由次元を保持する、正長の部分集合 bead の連結語。 -/
inductive SimplexHABeadWord (n : ℕ) : Fin (n + 1) → Fin (n + 1) → ℕ → Type
  | bead (I : Finset (Fin (n + 1))) (hI : 2 ≤ I.card) :
      SimplexHABeadWord n (I.min' (Finset.card_pos.mp (by omega)))
        (I.max' (Finset.card_pos.mp (by omega))) (I.card - 2)
  | join {a b c : Fin (n + 1)} {p q : ℕ}
      (left : SimplexHABeadWord n a b p) (right : SimplexHABeadWord n b c q) :
      SimplexHABeadWord n a c (p + q)

end SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
