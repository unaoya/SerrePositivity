module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroSourceArrows
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.InternalHomFlipVertices

/-! # 二本の辺から cospan の族を構成する

概要：共通の終点を持つ二本の辺の族を、実際の cospan の関手単体集合の族へ貼り合わせる。
方針：内部 Hom の二変数を交換し、cospan ホーンの pushout を適用して戻す。
規約：基底の単体集合に条件を課さない。
使われ方：S3 の loop の入力の相対延長。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：共通の終点の条件は、二変数を交換した辺の終点の一致を与える。
方針：終点の零単体を Yoneda と交換同型の評価公式で計算する。
規約：基底は任意。
使われ方：cospan の族の pushout の可換条件。 -/
lemma stable_intervalFamily_flip_target {A X : SSet.{u}}
    (L R : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (h : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :
    stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A Δ[1] X L =
      stdSimplex.δ (0 : Fin 2) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A Δ[1] X R := by
  apply SSet.yonedaEquiv.injective
  rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv_comp]
  have hδ : SSet.yonedaEquiv (stdSimplex.δ (0 : Fin 2) :
      (Δ[0] : SSet.{u}) ⟶ Δ[1]) = stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by decide
  rw [hδ]
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A Δ[1] X L).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A Δ[1] X R).app (Opposite.op ⦋0⦌)
      (stdSimplex.obj₀Equiv.symm (1 : Fin 2))
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero, _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.internalHomFlipHomEquiv_app_zero, h]

/-- 概要：終点を共有する二本の辺の族を cospan の族に貼り合わせる。
方針：交換した二本の辺をホーンの pushout へ降ろし、交換を戻す。
規約：第一辺は 0→2、第二辺は 1→2。
使われ方：loop の cospan の coherent な族。 -/
def stable_cospanFamilyOfArrows {A X : SSet.{u}}
    (L R : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X)
    (h : L ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      R ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (1 : Fin 2))) :
    A ⟶ (ihom (horn 2 2 : SSet.{u})).obj X :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A (horn 2 2 : SSet.{u}) X).symm
    (horn₂₂.isPushout.desc (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A Δ[1] X L)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A Δ[1] X R) (stable_intervalFamily_flip_target L R h))

/-- 概要：貼り合わせた cospan の族の第一辺は元の第一辺の族。
方針：二変数の交換の単射性と pushout の第一包含の式を使う。
規約：0→2 の辺。
使われ方：cospan の相対境界の回収。 -/
lemma stable_cospanFamilyOfArrows_left {A X : SSet.{u}}
    (L R : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (h) :
    stable_cospanFamilyOfArrows L R h ≫ (pre horn₂₂.ι₀₂).app X = L := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A Δ[1] X).injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  dsimp only [stable_cospanFamilyOfArrows]
  rw [Equiv.apply_symm_apply]
  exact horn₂₂.isPushout.inl_desc _ _ _

/-- 概要：貼り合わせた cospan の族の第二辺は元の第二辺の族。
方針：二変数の交換の単射性と pushout の第二包含の式を使う。
規約：0→2 の辺。
使われ方：cospan の相対境界の回収。 -/
lemma stable_cospanFamilyOfArrows_right {A X : SSet.{u}}
    (L R : A ⟶ (ihom (Δ[1] : SSet.{u})).obj X) (h) :
    stable_cospanFamilyOfArrows L R h ≫ (pre horn₂₂.ι₁₂).app X = R := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A Δ[1] X).injective
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app]
  dsimp only [stable_cospanFamilyOfArrows]
  rw [Equiv.apply_symm_apply]
  exact horn₂₂.isPushout.inr_desc _ _ _

/-- 概要：cospan の族は二本の辺への制限で決まる。
方針：二変数を交換してホーンの pushout の射の一意性を使う。
規約：基底・値域に条件は不要。
使われ方：cospan の族の厳密な境界一致。 -/
lemma stable_cospanFamily_hom_ext {A X : SSet.{u}}
    {f g : A ⟶ (ihom (horn 2 2 : SSet.{u})).obj X}
    (hL : f ≫ (pre horn₂₂.ι₀₂).app X = g ≫ (pre horn₂₂.ι₀₂).app X)
    (hR : f ≫ (pre horn₂₂.ι₁₂).app X = g ≫ (pre horn₂₂.ι₁₂).app X) : f = g := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A (horn 2 2 : SSet.{u}) X).injective
  apply horn₂₂.isPushout.hom_ext
  · have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A Δ[1] X) hL
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app] using h
  · have h := congrArg (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv A Δ[1] X) hR
    simpa only [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.internalHomFlipHomEquiv_pre_app] using h

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
