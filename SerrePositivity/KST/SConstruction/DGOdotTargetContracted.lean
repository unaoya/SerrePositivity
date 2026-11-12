module
public import SerrePositivity.KST.SConstruction.DGOdotTargetFunctor
public import SerrePositivity.DifferentialGraded.Quotient.Path.Evaluation

/-! # 元の対角像の指定収縮を持つ実 cone 関手
概要：元の対角像の実収縮元を、D β3 の ContractedFunctor へ渡す。
方針：像の各対象に前像を一つ固定し、その前像の既存収縮を等号で運ぶ。
規約：収縮を新たに選ばず、S 内の自然な零化も仮定しない。使われ方：実商からの延長。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory Limits DifferentialGraded InfinityCategories
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.source d)
local notation "C" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.left d)
local notation "D" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.right d)
local notation "E" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraCategory R (DGOdotInput.corner d)
local notation "L" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.top d)
local notation "G" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.side d)
local notation "p" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.lower d)
local notation "q" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgAlgebraMap R (DGOdotInput.upper d)
local notation "h" => dgOdotInput_dg_commutes R d
local notation "CL" => DGSmallPerfectArrowTarget R (A) (C) (L)
local notation "DR" => DGSmallPerfectArrowTarget R (A) (D) (G)
local notation "LS" => dgSmallPerfectArrow R (A) (C) (L)
local notation "GS" => dgSmallPerfectArrow R (A) (D) (G)
local notation "pS" => dgSmallPerfectSquareLeftMap R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "qS" => dgSmallPerfectSquareRightMap R (A) (C) (D) (E) (L) (G) (p) (q)
local notation "j" => dgSmallPerfectSquareDiagonal R (A) (C) (D) (E) (L) (G) (p) (q) (h)

/-- 同じ元の実 cone 関手と、選択した対角前像の既存収縮を持つ D β3 入力。 -/
def dgOdotTargetContractedFunctor :
    DGQuotient.ContractedFunctor R (DGOdotGluing R d)
      (dgQuotientImage R (dgOdotQuotientInput R d).diagonal)
      (PerfectDGModule R (DGOdotCorner R d)) where
  toDGFunctor := dgOdotTargetFunctor R d
  homotopy b := by
    let a : DGSmallPerfectBase R (A) := Classical.choose b.property
    have ha : (j).obj a = b.val := Classical.choose_spec b.property
    exact ha ▸ dgOdotTargetDiagonalContractingElement R d a
  d_homotopy b := by
    let a : DGSmallPerfectBase R (A) := Classical.choose b.property
    have ha : (j).obj a = b.val := Classical.choose_spec b.property
    have hd : ∀ (x : DGOdotGluing R d) (e : (j).obj a = x),
        (homObject R (PerfectDGModule R (DGOdotCorner R d))
          (dgOdotTargetCone R d x) (dgOdotTargetCone R d x)).d (-1) 0
          (e ▸ dgOdotTargetDiagonalContractingElement R d a) =
        (unitElement R (dgOdotTargetCone R d x)).val := by
      intro x e
      cases e
      exact dgOdotTargetDiagonalContractingElement_d R d a
    exact hd b.val ha

/-- 同じ指定収縮データの元の関手は、構成済みの実 cone 関手そのもの。 -/
lemma dgOdotTargetContractedFunctor_underlying :
    (dgOdotTargetContractedFunctor R d).toDGFunctor = dgOdotTargetFunctor R d := rfl

/-- 同じ像対象の収縮は、固定した前像の既存収縮を同じ対象等号で運んだもの。 -/
lemma dgOdotTargetContractedFunctor_homotopy
    (b : dgQuotientImage R (dgOdotQuotientInput R d).diagonal) :
    (dgOdotTargetContractedFunctor R d).homotopy b =
      let a : DGSmallPerfectBase R (A) := Classical.choose b.property
      let ha : (j).obj a = b.val := Classical.choose_spec b.property
      ha ▸ dgOdotTargetDiagonalContractingElement R d a := rfl

end SerrePositivity.KST.SConstruction
