module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorNuAbsoluteTriangle

/-!
概要：同じ絶対提示の元零化面の二つの二単体を、同じ固定 ν のまま取り出す。
方針：四辺と三頂点を回収し、元の二単体の端点 Hom を照合する。
規約：三角形を別の合成代表に置き換えない。
使われ方：実面の同じ高次データを保つ相対充填。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R) (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d)

/-- 概要：両二単体の始点は同じ元核の固定 ν 値。
方針：三角形の最初の頂点と実面の始点を照合する。
規約：同じ二単体の対象写像の等号。使われ方：豊穣 Hom の始域輸送。 -/
lemma dgOdotMilnorNuAbsoluteTriangle_source (j : Fin 2) :
    (dgOdotMilnorNuAbsoluteNullTriangle R d h j).obj ⟨ULift.up (0 : Fin 3)⟩ =
      dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d) := by
  let F := perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)
  let t := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 2} j)
  have hn := NatTrans.naturality_apply F
    (SimplexCategory.const ⦋0⦌ ⦋2⦌ (0 : Fin 3)).op t
  have hs : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}).map
      (SimplexCategory.const ⦋0⦌ ⦋2⦌ (0 : Fin 3)).op t =
        (stdSimplex.obj₀Equiv.symm (0 : Fin 2),
          stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
    fin_cases j <;> apply Prod.ext <;> apply SSet.stdSimplex.ext <;>
      intro i <;> fin_cases i <;> rfl
  have he : (dgOdotMilnorNuAbsoluteNullTriangle R d h j).obj ⟨ULift.up (0 : Fin 3)⟩ =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 0 0) := by
    have hn' := congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject hn
    rw [hs] at hn'
    exact hn'.symm
  rw [he]
  rw [(perfectVerdierRawSquare_vertices (dgOdotMilnorNuPerfectSequence R d h)).1,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
  rfl

/-- 概要：両二単体の終点は同じ元 resolved 商の固定 ν 値。
方針：三角形の最後の頂点と実面の終点を照合する。
規約：同じ二単体の対象写像の等号。使われ方：豊穣 Hom の終域輸送。 -/
lemma dgOdotMilnorNuAbsoluteTriangle_target (j : Fin 2) :
    (dgOdotMilnorNuAbsoluteNullTriangle R d h j).obj ⟨ULift.up (2 : Fin 3)⟩ =
      dgKInputStableValue R (dgOdotMilnorResolvedInput R d) := by
  let F := perfectVerdierRawSquare (dgOdotMilnorNuPerfectSequence R d h)
  let t := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.squareTriangle.{u + 2} j)
  have hn := NatTrans.naturality_apply F
    (SimplexCategory.const ⦋0⦌ ⦋2⦌ (2 : Fin 3)).op t
  have hs : (Δ[1] ⊗ Δ[1] : SSet.{u + 2}).map
      (SimplexCategory.const ⦋0⦌ ⦋2⦌ (2 : Fin 3)).op t =
        (stdSimplex.obj₀Equiv.symm (1 : Fin 2),
          stdSimplex.obj₀Equiv.symm (1 : Fin 2)) := by
    fin_cases j <;> apply Prod.ext <;> apply SSet.stdSimplex.ext <;>
      intro i <;> fin_cases i <;> rfl
  have he : (dgOdotMilnorNuAbsoluteNullTriangle R d h j).obj ⟨ULift.up (2 : Fin 3)⟩ =
      _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject (_root_.SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.squareVertex F 1 1) := by
    have hn' := congrArg _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject hn
    rw [hs] at hn'
    exact hn'.symm
  rw [he]
  rw [(perfectVerdierRawSquare_vertices (dgOdotMilnorNuPerfectSequence R d h)).2.2.1,
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.stableObject_vertex]
  rfl

/-- 概要：元の実二単体の全 Hom データを同じ核と resolved 商の Hom で読む。
方針：元の豊穣関手の Hom 作用を、証明済みの端点等号で輸送する。
規約：元の二単体の Hom 写像を変更しない。使われ方：零合成空間への因子分解。 -/
def dgOdotMilnorNuAbsoluteTriangleHom (j : Fin 2) :
    nerve (CategoryTheory.SimplicialThickening.Path
      (ULift.up.{u + 1} (0 : Fin 3)) (ULift.up.{u + 1} (2 : Fin 3))) ⟶
        SimplicialCategory.sHom (C := _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1})
          (dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d))
          (dgKInputStableValue R (dgOdotMilnorResolvedInput R d)) :=
  (dgOdotMilnorNuAbsoluteNullTriangle R d h j).map ⟨ULift.up (0 : Fin 3)⟩
    ⟨ULift.up (2 : Fin 3)⟩ ≫
      eqToHom (congrArg₂ (fun X Y : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Infinity.StableQCat.{u + 1} => SimplicialCategory.sHom X Y)
        (dgOdotMilnorNuAbsoluteTriangle_source R d h j)
        (dgOdotMilnorNuAbsoluteTriangle_target R d h j))

end SerrePositivity.KST.SConstruction
