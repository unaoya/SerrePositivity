module

public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.FrontHom

/-!
概要：coherent nerve の右 pinched 単体と旗の解像からの写像の同値。
方針：非定値な Hom、固定面の Hom、自己 Hom をそれぞれ回収して豊穣関手の外延性を使う。
規約：単体的圏の局所 Kan 性は不要。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、補助解像による写像の普遍性。

対応節は Kerodon 2.4（Tag 00JN）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u v
open CategoryTheory SimplicialThickening MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories

/-- 概要：端点を共通の対象に正規化した Hom の作用の等号から元の等号を得る。
方針：対象の等号を全て消去して恒等の移送に帰着する。
規約：移送後の終域が等しい単体集合の射を比較する。
使われ方：Kerodon §2.4.3（Tag 00KM）、豊穣関手の Hom の回収における等号の整理。 -/
lemma simplicialHom_normalized_ext {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {D : SSet.{u}} {A B A' B' X Y : C} (hA : A = A') (hB : B = B')
    (ha : A' = X) (hb : B' = Y) (f : D ⟶ SimplicialCategory.sHom A B)
    (g : D ⟶ SimplicialCategory.sHom A' B')
    (h : f ≫ eqToHom (congrArg₂ SimplicialCategory.sHom (hA.trans ha) (hB.trans hb)) =
      g ≫ eqToHom (congrArg₂ SimplicialCategory.sHom ha hb)) :
    f ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) = g := by
  subst A'
  subst B'
  subst X
  subst Y
  simpa using h

/-- 概要：simplicial thickening の自己 Hom の作用は豊穣恒等に定値。
方針：自己 path は恒等 path しか持たないので豊穣関手の単位則を評価する。
規約：対象の等号による正規化を含む。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、最後の自己 Hom の回収。 -/
lemma enrichedFunctor_thickening_self_map {J : Type u} [LinearOrder J]
    {C : Type v} [Category.{u} C] [SimplicialCategory C]
    (T : EnrichedFunctor SSet.{u} (SimplicialThickening J) C) (a : J)
    {X : C} (ha : T.obj ⟨a⟩ = X) :
    T.map ⟨a⟩ ⟨a⟩ ≫ eqToHom (congrArg₂ SimplicialCategory.sHom ha ha) =
      toUnit _ ≫ eId SSet X := by
  subst X
  simp only [eqToHom_refl, Category.comp_id]
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  have hP : P = (eId SSet (⟨a⟩ : SimplicialThickening J)).app d PUnit.unit := by
    apply CategoryTheory.Functor.ext (fun k ↦ _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.thickeningPath_end_eq_id a (P.obj k))
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (T.map_id ⟨a⟩) d) PUnit.unit
  change (T.map ⟨a⟩ ⟨a⟩).app d
    ((eId SSet (⟨a⟩ : SimplicialThickening J)).app d PUnit.unit) = _ at h
  rw [← hP] at h
  exact h

/-- 概要：旗から作った単体の最後の自己 Hom は豊穣恒等に定値。
方針：最後の二つの分岐を展開して移送を消去する。
規約：両端点を終域の対象 Y に正規化する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、pinched 単体側の逆性の終域の部分。 -/
lemma coherentFlagHom_last_last {C : Type v} [Category.{u} C] [SimplicialCategory C]
    {X Y : C} {n : ℕ}
    (φ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentFlagHom φ (Fin.last (n + 1)) (Fin.last (n + 1)) ≫
      eqToHom (congrArg₂ SimplicialCategory.sHom
        (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n)) =
      toUnit _ ≫ eId SSet Y := by
  simp -implicitDefEqProofs +instances [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentFlagHom, _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj]

/-- 概要：pinched 単体を旗の写像へ移し、戻すと元の単体を回収する。
方針：端点の四つの場合で正規化した Hom の作用を比較する。
規約：固定面と固定終点も証明の一意性により回収する。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、写像の普遍性の pinched 単体側の逆性。 -/
lemma coherentFlagPinchedSimplex_flagMap {C : Type v} [Category.{u} C]
    [SimplicialCategory C] {X Y : C} {n : ℕ}
    (τ : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) n) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentFlagPinchedSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap τ) = τ := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  have hobj : ∀ a : SimplicialThickening (ULift.{u} (Fin (n + 2))),
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentFlagSimplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap τ)).obj a = τ.val.obj a := by
    rintro ⟨⟨a⟩⟩
    induction a using Fin.lastCases with
    | last => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_last X Y n).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinched_targetObj τ).symm
    | cast a => exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentHomComparisonObj_cast X Y a).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinched_sourceObj τ a).symm
  apply EnrichedFunctor.ext SSet hobj
  rintro ⟨⟨a⟩⟩ ⟨⟨b⟩⟩
  induction a using Fin.lastCases <;> induction b using Fin.lastCases
  case last.last =>
    apply simplicialHom_normalized_ext (hobj _) (hobj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinched_targetObj τ)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinched_targetObj τ)
    exact (coherentFlagHom_last_last (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap τ)).trans
      (enrichedFunctor_thickening_self_map τ.val _ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinched_targetObj τ)).symm
  case last.cast b =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := SimplicialThickening.Path.le (P.obj 0)
    change n + 1 ≤ b.val at h
    have hb := b.isLt
    omega
  case cast.last a =>
    apply simplicialHom_normalized_ext (hobj _) (hobj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinched_sourceObj τ a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinched_targetObj τ)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentFlagHom_cast_last (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap τ) a).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pathResolutionMap_coherentPinchedFlagMap τ a)
  case cast.cast a b =>
    apply simplicialHom_normalized_ext (hobj _) (hobj _) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinched_sourceObj τ a)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinched_sourceObj τ b)
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentFlagHom_cast_cast (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap τ) a b).trans
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinched_sourceMap_full τ a b).symm

/-- 概要：右 pinched な coherent 単体と旗の解像から豊穣 Hom への射の同値。
方針：構成した二方向の変換と両側の回収則を組み合わせる。
規約：次数 n を固定した型の同値。次数の自然性は別途扱う。
使われ方：Kerodon Corollary 4.6.7.16（Tag 01LQ）、補助解像による写像の普遍性。 -/
noncomputable def coherentPinchedFlagEquiv {C : Type v} [Category.{u} C]
    [SimplicialCategory C] (X Y : C) (n : ℕ) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex X) (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex Y) n ≃
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentResolutionSimplex.{u} n ⟶ SimplicialCategory.sHom X Y) where
  toFun := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentPinchedFlagMap
  invFun := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentFlagPinchedSimplex
  left_inv := coherentFlagPinchedSimplex_flagMap
  right_inv := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.coherentPinchedFlagMap_flag

end SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories
