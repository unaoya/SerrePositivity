module

public import SerrePositivity.KST.Spectra.OmegaSpectrum
public import SerrePositivity.KST.Spectra.PointedMappingNaturality
public import SerrePositivity.Spectra.PointedSimplicialSet.SmashUnderlying

/-!
概要：Ω スペクトルの厳密な射と点つき写像空間の零次単体。
方針：段ごとの点つき射の可換条件を定め、内部 Hom の点による表示と比較する。
規約：合成は通常の射の段ごとの合成。
使われ方：BF 1978 §2、HTT A.3.3。単体的圏の基礎となる通常の圏。
-/

@[expose] public section

universe u

open CategoryTheory MonoidalCategory MonoidalClosed
open scoped Simplicial

namespace SerrePositivity.KST.Spectra

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：通常の点つき射を点つき写像空間の頂点として表す。
方針：閉構造の curry' と零次球面の非基点の頂点を用いる。
規約：実際の同値であり追加の入力条件は不要。
使われ方：BF 1978 §2、HTT A.3.3。スペクトルの厳密射との照合。 -/
def pointedHomVertexEquiv (X Y : PointedSimplicialSet.{u}) :
    (X ⟶ Y) ≃ (PointedObject.basedHom X Y).right _⦋0⦌ :=
  MonoidalClosed.curryHomEquiv'.trans (PointedSimplicialSet.unitVertexEquiv _)

/-- 概要：頂点の表示は源の制限を通常の合成へ移す。
方針：点つき制限の curry' の計算と頂点の自然性を用いる。
規約：pre は相対充填で使った等化子の制限。
使われ方：BF 1978 §2。スペクトルの構造射との可換条件。 -/
@[simp]
theorem pointedHomVertexEquiv_pre {X Y Z : PointedSimplicialSet.{u}}
    (i : X ⟶ Y) (f : Y ⟶ Z) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Z).app _ (pointedHomVertexEquiv Y Z f) =
      pointedHomVertexEquiv X Z (i ≫ f) := by
  dsimp only [pointedHomVertexEquiv, Equiv.trans_apply, MonoidalClosed.curryHomEquiv']
  change (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Z).right.app _
      (PointedSimplicialSet.unitVertexEquiv _ (MonoidalClosed.curry' f)) = _
  rw [← PointedSimplicialSet.unitVertexEquiv_naturality, PointedMapping.curry'_pre]
  rfl

/-- 概要：頂点の表示は標的での合成を通常の合成へ移す。
方針：内部 Hom の curry' の計算と頂点の自然性を用いる。
規約：通常の点つき射 f と g。
使われ方：BF 1978 §2。境界比較射の頂点での作用。 -/
@[simp]
theorem pointedHomVertexEquiv_post {X Y Z : PointedSimplicialSet.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (PointedObject.basedHomMap X g).right.app _ (pointedHomVertexEquiv X Y f) =
      pointedHomVertexEquiv X Z (f ≫ g) := by
  dsimp only [pointedHomVertexEquiv, Equiv.trans_apply, MonoidalClosed.curryHomEquiv']
  change ((ihom X).map g).right.app _
      (PointedSimplicialSet.unitVertexEquiv _ (MonoidalClosed.curry' f)) = _
  rw [← PointedSimplicialSet.unitVertexEquiv_naturality, MonoidalClosed.curry'_ihom_map]
  rfl

/-- 概要：suspension の写像空間への作用は頂点で通常の suspension を与える。
方針：suspensionHom_curry' と頂点の自然性を用いる。
規約：全単体次数の射に対する零次の計算。
使われ方：BF 1978 §2。構造射との可換条件の照合。 -/
@[simp]
theorem pointedHomVertexEquiv_suspension {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    (suspensionHom X Y).right.app _ (pointedHomVertexEquiv X Y f) =
      pointedHomVertexEquiv (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y)
        (PointedSimplicialSet.circle.{u} ◁ f) := by
  dsimp only [pointedHomVertexEquiv, Equiv.trans_apply, MonoidalClosed.curryHomEquiv']
  change (suspensionHom X Y).right.app _
      (PointedSimplicialSet.unitVertexEquiv (PointedObject.basedHom X Y)
        (MonoidalClosed.curry' f)) =
    PointedSimplicialSet.unitVertexEquiv (PointedObject.basedHom (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension X) (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.suspension Y))
      (MonoidalClosed.curry' (PointedSimplicialSet.circle.{u} ◁ f))
  rw [← PointedSimplicialSet.unitVertexEquiv_naturality, suspensionHom_curry']

namespace OmegaSpectrum

/-- 概要：Ω スペクトルの厳密な射。
方針：各段の点つき射と構造射との可換条件を束ねる。
規約：ホモトピー可換ではなく厳密可換。
使われ方：BF 1978 §2、HTT A.3.3。Sp の通常の射。 -/
structure Hom (X Y : OmegaSpectrum.{u}) where
  /-- 概要：段ごとの点つき射。
  方針：点つき単体集合の通常の射を使う。
  規約：同じ自然数次数の段。
  使われ方：BF 1978 §2。 -/
  app : ∀ n, (X.level n).space ⟶ (Y.level n).space
  /-- 概要：構造射との厳密な可換条件。
  方針：smash による suspension の作用で表す。
  規約：全ての自然数 n。
  使われ方：BF 1978 §2。 -/
  comm : ∀ n, PointedSimplicialSet.circle.{u} ◁ app n ≫ Y.sigma n = X.sigma n ≫ app (n + 1)

/-- 概要：スペクトルの射は段ごとの射で決まる。
方針：構造条件の証明の一意性を使う。
規約：全段での等式を入力する。
使われ方：BF 1978 §2。厳密な圏の法則。 -/
@[ext]
theorem Hom.ext {X Y : OmegaSpectrum.{u}} {f g : Hom X Y} (h : ∀ n, f.app n = g.app n) : f = g := by
  cases f
  cases g
  congr 1
  funext n
  exact h n

/-- 概要：Ω スペクトルの厳密な射からなる通常の圏。
方針：段ごとに恒等射と合成を取る。
規約：写像空間の豊穣構造との照合は別途行う。
使われ方：BF 1978 §2、HTT A.3.3。単体的圏の基礎。 -/
instance category : Category OmegaSpectrum.{u} where
  Hom := Hom
  id X := ⟨fun n ↦ 𝟙 (X.level n).space, by intro n; simp⟩
  comp f g := ⟨fun n ↦ f.app n ≫ g.app n, by
    intro n
    rw [whiskerLeft_comp, Category.assoc, g.comm, ← Category.assoc, f.comm, Category.assoc]⟩
  id_comp f := by apply Hom.ext; intro n; exact Category.id_comp _
  comp_id f := by apply Hom.ext; intro n; exact Category.comp_id _
  assoc f g h := by apply Hom.ext; intro n; exact Category.assoc _ _ _

end OmegaSpectrum

end

end SerrePositivity.KST.Spectra
