module

public import SerrePositivity.EInfinity.SimplicialLocalization.ResolutionWordEdge

/-!
# 零次の局所化から連結成分の圏への関手

概要：Dwyer–Kan の零次の局所化の全射を同じ Hom の連結成分へ送る。
方針：標準対象の同じ表示で射を移し、元の単位・合成を商へ降ろす。
規約：形式逆も含む零次の全ての射を扱う。
使われ方：弱同値の反転と普通の局所化との比較の逆関手。
-/

@[expose] public section

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace SerrePositivity.EInfinity.SimplicialLocalization

open CategoryTheory Opposite
open scoped Simplicial

variable (C : _root_.SerrePositivity.InfinityCategories.Kerodon.AdjointFunctors.Localization.RelativeCategory.{u})

/-- 概要：零次の局所化の元の射を固定 Hom の零単体へ送る（Dwyer–Kan）。
方針：元の射を同じ標準対象表示で前後から移す。
規約：生成射だけでなく零次の局所化の全射を含む。
使われ方：連結成分への零次関手。 -/
def localizationZeroHom {X Y : C.category}
    (f : C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj X) ⟶
      C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj Y)) :
    (localizationHom C X Y) _⦋0⦌ :=
  eqToHom (localizedFreeResolutionObject_zero C X) ≫ f ≫
    eqToHom (localizedFreeResolutionObject_zero C Y).symm

/-- 概要：零次の表示は恒等射を保つ（Dwyer–Kan）。
方針：同じ対象移送の順逆を相殺する。
規約：元の零次の恒等射。
使われ方：零次の連結成分関手の単位則。 -/
lemma localizationZeroHom_id (X : C.category) :
    localizationZeroHom C (𝟙 (C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj X))) =
      𝟙 (localizedFreeResolutionObject C (op ⦋0⦌) X) := by
  simp [localizationZeroHom]

/-- 概要：零次の表示は全ての射の合成を保つ（Dwyer–Kan）。
方針：中間対象の同じ移送の順逆を相殺する。
規約：形式逆を含む元の合成。
使われ方：零次の連結成分関手の合成則。 -/
lemma localizationZeroHom_comp {X Y Z : C.category}
    (f : C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj X) ⟶
      C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj Y))
    (g : C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj Y) ⟶
      C.weakEquivalences.paths.Q.obj ((Paths.of C.category).obj Z)) :
    localizationZeroHom C (f ≫ g) = localizationZeroHom C f ≫ localizationZeroHom C g := by
  simp [localizationZeroHom, Category.assoc]

/-- 概要：零次の局所化から同じ DK Hom の連結成分への関手（Dwyer–Kan）。
方針：元の局所化の対象の標準表示と射の零単体の類を使う。
規約：零次の局所化の全ての射を保持する。
使われ方：元の指定矢の反転と比較の同値性。 -/
def zeroLevelComponentsFunctor : C.weakEquivalences.paths.Localization ⥤ LocalizationComponents C
    where
  obj X := (Localization.Construction.objEquiv C.weakEquivalences.paths).symm X
  map f := SSet.π₀.mk (localizationZeroHom C f)
  map_id _ := congrArg SSet.π₀.mk (localizationZeroHom_id C _)
  map_comp f g := congrArg SSet.π₀.mk (localizationZeroHom_comp C f g)

/-- 概要：零次の生成射の像は同じ一文字の射の類（Dwyer–Kan）。
方針：元の対象と零単体の表示の定義を評価する。
規約：元の生成射を保持する。
使われ方：弱同値の反転の同定。 -/
lemma zeroLevelComponentsFunctor_arrow {X Y : C.category} (f : X ⟶ Y) :
    (zeroLevelComponentsFunctor C).map
        (C.weakEquivalences.paths.Q.map ((Paths.of C.category).map f)) =
      localizationArrowClass C f := rfl

/-- 概要：零次の自由な列の比較は元の生成関手で因子化する（Dwyer–Kan）。
方針：列をその合成の一文字へ結ぶ同じ一次の辺を使う。
規約：元の列の合成を保持する厳密な関手等式。
使われ方：普通の局所化からの逆関手の一意性。 -/
lemma zeroLevelComponentsFunctor_fac :
    C.weakEquivalences.paths.Q ⋙ zeroLevelComponentsFunctor C =
      pathComposition C.category ⋙ localizationComponentsQ C := by
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro X Y p
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact (localizationResolutionWordClass C p).symm

end SerrePositivity.EInfinity.SimplicialLocalization
