module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuProjectionNullBoundary
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TrianglePathInterval

/-!
概要：元両二単体の全 path Hom を既存の区間同型で厳密に表示する。
方針：F1 正本の同型を使い、両端を元共有対角と元最大合成へ戻す。
規約：全 Hom を区間のトレースだけへ弱めない。使われ方：混合零 Hom の比較正方形。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial

/-- 概要：元の全 path nerve と標準区間の同じ厳密同型。
方針：F1 の native path の同型を特殊化する。
規約：前向き・逆向きとも全単体を保持。使われ方：元全 Hom の区間表示。 -/
abbrev dgOdotMilnorNuNullPathIntervalIso :
    nerve DGOdotMilnorNuNullTrianglePath.{u} ≅ (Δ[1] : SSet.{u + 1}) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso.{u + 1}

/-- 概要：標準始点は元上下二単体の同じ共有対角 path。
方針：元最小 path の台と両端点から逆関手の元対象を照合する。
規約：元 path の等号。使われ方：混合正方形の共有対角境界。 -/
lemma dgOdotMilnorNuNullPathIntervalIso_source :
    dgOdotMilnorNuNullPathIntervalIso.{u}.inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullDiagonalPath.{u} := by
  apply CategoryTheory.Functor.ext (fun _ => ?_)
  change _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathFromInterval (ULift.up (0 : Fin 2)) = dgOdotMilnorNuNullDiagonalPath.{u}
  apply SimplicialThickening.Path.ext
  apply Set.Subset.antisymm
  · rintro ⟨x⟩ hx
    change x = 0 ∨ x = 2 ∨ (0 : Fin 2) = 1 at hx
    simp only [Fin.zero_ne_one, or_false] at hx
    rcases hx with rfl | rfl
    · exact dgOdotMilnorNuNullDiagonalPath.{u}.left
    · exact dgOdotMilnorNuNullDiagonalPath.{u}.right
  · exact (dgOdotMilnorNuNullDiagonalToPath
      (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.trianglePathFromInterval (ULift.up (0 : Fin 2)))).1.1.1

/-- 概要：標準終点は元二短辺の同じ最大合成 path。
方針：F1 の元全 path と区間全体の台を照合する。
規約：元 path の等号。使われ方：指定商比較との合成端の貼り合わせ。 -/
lemma dgOdotMilnorNuNullPathIntervalIso_target :
    dgOdotMilnorNuNullPathIntervalIso.{u}.inv.app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex dgOdotMilnorNuNullUpperMaximalPath.{u} := by
  have hp : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleFullPath.{u + 1} = dgOdotMilnorNuNullUpperMaximalPath.{u} := by
    apply SimplicialThickening.Path.ext
    ext ⟨x⟩
    change True ↔ (0 ≤ x ∧ x ≤ 2)
    exact iff_of_true trivial ⟨Fin.zero_le _, Fin.le_last _⟩
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.triangleNativePathIntervalIso_inv_last.trans (congrArg ComposableArrows.mk₀ hp)

variable (R : Type u) [CommRing R] (d : DGOdotInput R)

/-- 概要：元実二単体の全 Hom の同じ零成分内の区間表示。
方針：既存の区間逆同型で元の全因子分解を制限する。
規約：元二胞体の全 Hom を回収可能。使われ方：比較正方形の実側の辺。 -/
def dgOdotMilnorNuNullTriangleInterval (j : Fin 2) :
    (Δ[1] : SSet.{u + 1}) ⟶ DGOdotMilnorNuNullCoherenceSpace R d :=
  dgOdotMilnorNuNullPathIntervalIso.inv ≫ dgOdotMilnorNuNullTriangleFactor R d j

/-- 概要：元実二単体の区間表示から元の全 Hom 因子分解を厳密回収する。
方針：元同型の順逆合成式を使う。
規約：全単体の等号。使われ方：元二胞体を保つ比較。 -/
lemma dgOdotMilnorNuNullTriangleInterval_recover (j : Fin 2) :
    dgOdotMilnorNuNullPathIntervalIso.hom ≫ dgOdotMilnorNuNullTriangleInterval R d j =
      dgOdotMilnorNuNullTriangleFactor R d j :=
  dgOdotMilnorNuNullPathIntervalIso.hom_inv_id_assoc _

/-- 概要：元絶対二単体の全 Hom の同じ零成分内の区間表示。
方針：同じ区間逆同型を元絶対側の全因子分解に適用する。
規約：元の絶対二胞体を保持。使われ方：比較正方形の絶対側の辺。 -/
def dgOdotMilnorNuAbsoluteTriangleInterval (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) (j : Fin 2) :
    (Δ[1] : SSet.{u + 1}) ⟶ DGOdotMilnorNuNullCoherenceSpace R d :=
  dgOdotMilnorNuNullPathIntervalIso.inv ≫ dgOdotMilnorNuAbsoluteTriangleFactor R d h j

/-- 概要：元絶対二単体の全 Hom 因子分解を同じ区間表示から厳密回収する。
方針：元同型の順逆合成式を使う。
規約：全単体の等号。使われ方：指定絶対面の保持。 -/
lemma dgOdotMilnorNuAbsoluteTriangleInterval_recover (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)
    (j : Fin 2) :
    dgOdotMilnorNuNullPathIntervalIso.hom ≫ dgOdotMilnorNuAbsoluteTriangleInterval R d h j =
      dgOdotMilnorNuAbsoluteTriangleFactor R d h j :=
  dgOdotMilnorNuNullPathIntervalIso.hom_inv_id_assoc _

end SerrePositivity.KST.SConstruction
