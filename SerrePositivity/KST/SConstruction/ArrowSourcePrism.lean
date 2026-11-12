module
public import SerrePositivity.KST.SConstruction.VariableTimeHomotopy
public import SerrePositivity.KST.SConstruction.FunctorVertexEvaluation

/-! # 恒等な始点の辺から元の辺への普遍 prism
概要：辺 f:x→y に対し id_x から f への自然変換を全ての辺の族で構成する。
方針：二つの区間の最小値で辺を評価する。
規約：始点の成分は厳密に恒等。使われ方：cofiber 射影で持ち上げる McCarthy の λ→ν。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory MonoidalCategory CartesianMonoidalCategory MonoidalClosed SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：全ての辺について恒等な始点の辺から元の辺へ進む prism。
方針：内側の辺の座標と外側の時刻の最小値で評価する。
規約：外側の時刻は第一因子。使われ方：McCarthy の cofiber の比較の基底。 -/
def arrowSourcePrism (C : SSet.{u}) :
    (Δ[1] : SSet.{u}) ⊗ (ihom (Δ[1] : SSet.{u})).obj C ⟶ (ihom (Δ[1] : SSet.{u})).obj C :=
  curry ((α_ (Δ[1] : SSet.{u}) Δ[1] ((ihom (Δ[1] : SSet.{u})).obj C)).inv ≫
    (intervalMin ▷ ((ihom (Δ[1] : SSet.{u})).obj C)) ≫ (ihom.ev (Δ[1] : SSet.{u})).app C)

/-- 概要：普遍 prism の始点は始点で一定な辺。
方針：最小値の第二座標零の式を使う。
規約：quasicategory 性は不要。使われ方：λ の入力の同定。 -/
lemma arrowSourcePrism_zero (C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 ((ihom (Δ[1] : SSet.{u})).obj C) ≫ arrowSourcePrism C =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) ≫
        curry (snd (Δ[1] : SSet.{u}) C) := by
  apply uncurry_injective
  rw [arrowSourcePrism, uncurry_natural_left, uncurry_curry,
    uncurry_natural_left, uncurry_curry]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, F⟩
  change F.app (Opposite.op ⦋n⦌) (𝟙 _) (intervalMin.app (Opposite.op ⦋n⦌)
    (s, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n)) = _
  rw [intervalMin_app_zero]
  rfl

/-- 概要：普遍 prism の終点は元の辺の関手の恒等射。
方針：最小値の第二座標一の式を使う。
規約：全ての高次単体での等号。使われ方：ν の入力の同定。 -/
lemma arrowSourcePrism_one (C : SSet.{u}) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 1 ((ihom (Δ[1] : SSet.{u})).obj C) ≫ arrowSourcePrism C = 𝟙 _ := by
  apply uncurry_injective
  rw [arrowSourcePrism, uncurry_natural_left, uncurry_curry, uncurry_id_eq_ev]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨s, F⟩
  change F.app (Opposite.op ⦋n⦌) (𝟙 _) (intervalMin.app (Opposite.op ⦋n⦌)
    (s, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 1) n)) = _
  rw [intervalMin_app_one]
  rfl

/-- 概要：普遍 prism の始点の成分は元の始点で一定。
方針：内側の座標零と任意の時刻の最小値は零。
規約：prism 全体で厳密に一定。使われ方：ρ の subobject を厳密に制御する。 -/
lemma arrowSourcePrism_source (C : SSet.{u}) :
    arrowSourcePrism C ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) =
      snd (Δ[1] : SSet.{u}) ((ihom (Δ[1] : SSet.{u})).obj C) ≫
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.evaluateFunctorAt (stdSimplex.obj₀Equiv.symm (0 : Fin 2)) := by
  rw [arrowSourcePrism, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.curry_evaluateFunctorAt_interval]
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨t, F⟩
  have ht : intervalMin.app (Opposite.op ⦋n⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n, t) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n := by
    apply stdSimplex.ext
    intro j
    change min (0 : Fin 2) (t j) = 0
    exact min_eq_left (Fin.zero_le _)
  change F.app (Opposite.op ⦋n⦌) (𝟙 _) (intervalMin.app (Opposite.op ⦋n⦌)
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n, t)) = _
  rw [ht]
  rfl

end SerrePositivity.KST.SConstruction
