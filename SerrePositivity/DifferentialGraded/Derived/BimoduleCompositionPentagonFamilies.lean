module
public import SerrePositivity.DifferentialGraded.Derived.BimoduleCompositionFamilies

/-! # 五角の両経路の任意のパラメータ族に関する自然性

## 概要
五角の両経路の任意のパラメータ族に関する自然性。

## 方針
semifree・K-flatモデルと指定準同型局所化の計算を組み合わせ、既存の主導来関手を保持する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleCompositionPentagon.lean。
固定dg圏上の導来tensor・Morita作用の基盤。非平坦Homの分解source上でも同じ計算APIを再利用できる。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z t x s s'
namespace SerrePositivity.DifferentialGraded.BimoduleTensor
open CategoryTheory CategoryTheory.Functor
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w) (E : Type z)
  (F : Type t) (G : Type x)
  [DGCategory A B] [DGCategory A C] [DGCategory A E] [DGCategory A F] [DGCategory A G]
  [Small.{u} B] [Small.{u} C] [Small.{u} E] [Small.{u} F] [Small.{u} G]
variable {T : Type s} [Category.{s'} T]
variable (hE : localHomKFlat A E) (hF : localHomKFlat A F) (hG : localHomKFlat A G)
  (Q : T ⥤ DerivedBimoduleCategory A C E) (R : T ⥤ DerivedBimoduleCategory A E F)
  (S : T ⥤ DerivedBimoduleCategory A F G)

def derivedBimodulePentagonShortFamily :
    compositionFamily
        (compositionFamily (Q ⋙ derivedBimoduleComposeFunctor A B C E hE)
          (R ⋙ derivedBimoduleComposeFunctor A B E F hF))
        (S ⋙ derivedBimoduleComposeFunctor A B F G hG) ⟶
      derivedBimoduleComposeFamily A C E G hG Q
        (derivedBimoduleComposeFamily A E F G hG R S) ⋙
          derivedBimoduleComposeFunctor A B C G hG :=
  (compositionFamilyAssociator (Q ⋙ derivedBimoduleComposeFunctor A B C E hE)
      (R ⋙ derivedBimoduleComposeFunctor A B E F hF)
      (S ⋙ derivedBimoduleComposeFunctor A B F G hG)).hom ≫
    compositionFamilyMap (𝟙 (Q ⋙ derivedBimoduleComposeFunctor A B C E hE))
      (derivedBimoduleAssociatorFamily A B E F G hF hG R S).hom ≫
    (derivedBimoduleAssociatorFamily A B C E G hE hG Q
      (derivedBimoduleComposeFamily A E F G hG R S)).hom

def derivedBimodulePentagonLongFamily :
    compositionFamily
        (compositionFamily (Q ⋙ derivedBimoduleComposeFunctor A B C E hE)
          (R ⋙ derivedBimoduleComposeFunctor A B E F hF))
        (S ⋙ derivedBimoduleComposeFunctor A B F G hG) ⟶
      derivedBimoduleComposeFamily A C E G hG Q
        (derivedBimoduleComposeFamily A E F G hG R S) ⋙
          derivedBimoduleComposeFunctor A B C G hG :=
  compositionFamilyMap (derivedBimoduleAssociatorFamily A B C E F hE hF Q R).hom
      (𝟙 (S ⋙ derivedBimoduleComposeFunctor A B F G hG)) ≫
    (derivedBimoduleAssociatorFamily A B C F G hF hG
      (derivedBimoduleComposeFamily A C E F hF Q R) S).hom ≫
    whiskerRight (derivedBimoduleInnerAssociatorFamily A C E F G hF hG Q R S).hom
      (derivedBimoduleComposeFunctor A B C G hG)

lemma derivedBimodulePentagonShortFamily_app (i : T) :
    (derivedBimodulePentagonShortFamily A B C E F G hE hF hG Q R S).app i =
      derivedBimodulePentagonShort A B C E F G hE hF hG (Q.obj i) (R.obj i) (S.obj i) := by
  ext P
  dsimp [derivedBimodulePentagonShortFamily, compositionFamilyMap, compositionFamilyAssociator,
    compositionFamily, derivedBimoduleComposeFamily, derivedBimoduleAssociatorFamily,
    derivedBimodulePentagonShort, uncurry, whiskeringLeft]
  simp only [CategoryTheory.Functor.map_id, Category.id_comp]

lemma derivedBimodulePentagonLongFamily_app (i : T) :
    (derivedBimodulePentagonLongFamily A B C E F G hE hF hG Q R S).app i =
      derivedBimodulePentagonLong A B C E F G hE hF hG (Q.obj i) (R.obj i) (S.obj i) := by
  ext P
  dsimp [derivedBimodulePentagonLongFamily, compositionFamilyMap, derivedBimoduleComposeFamily,
    derivedBimoduleAssociatorFamily, derivedBimoduleInnerAssociatorFamily,
    derivedBimodulePentagonLong, uncurry, whiskeringLeft]
  simp only [Category.comp_id]

end SerrePositivity.DifferentialGraded.BimoduleTensor
