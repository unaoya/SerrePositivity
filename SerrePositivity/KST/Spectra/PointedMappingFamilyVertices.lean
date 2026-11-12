module

public import SerrePositivity.KST.Spectra.PointedMappingParameters
public import SerrePositivity.KST.Spectra.SphereHomotopy

/-!
概要：点つき内部 Hom の頂点を通常のパラメータ付き curry で表示する。
方針：零次標準単体との積の射影とその切断を用いて、等化子の普遍性で同値を作る。
規約：標的の Kan 性を仮定しない。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。球面の写像族の端点の計算。
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra.PointedMapping

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：零次標準単体の唯一の頂点を付ける切断。
方針：恒等射と零次頂点への定数射の積を使う。
規約：基点を付けない単体集合の操作。
使われ方：Goerss–Jardine I §7。パラメータ付き射を一点で評価する。 -/
def zeroSection (X : SSet.{u}) : X ⟶ X ⊗ (Δ[0] : SSet.{u}) :=
  lift (𝟙 X) (SSet.const (stdSimplex.obj₀Equiv.symm 0))

/-- 概要：零次パラメータの切断を射影すると恒等射。
方針：積の第一成分を計算する。
規約：任意の単体集合 X。
使われ方：Goerss–Jardine I §7。頂点表示の逆写像の検査。 -/
@[reassoc (attr := simp)]
theorem zeroSection_fst (X : SSet.{u}) : zeroSection X ≫ fst X (Δ[0] : SSet.{u}) = 𝟙 X := rfl

/-- 概要：零次パラメータでは射影と切断の逆順の合成も恒等射。
方針：第二成分の値は零次標準単体の一意性で一致する。
規約：単体集合の射の厳密な等式。
使われ方：Goerss–Jardine I §7。パラメータ付き curry の頂点の全単射性。 -/
@[reassoc (attr := simp)]
theorem fst_zeroSection (X : SSet.{u}) : fst X (Δ[0] : SSet.{u}) ≫ zeroSection X = 𝟙 _ := by
  apply NatTrans.ext
  funext ⟨⟨d⟩⟩
  apply ConcreteCategory.hom_ext
  rintro ⟨x, t⟩
  apply Prod.ext
  · rfl
  · apply stdSimplex.ext
    intro j
    apply Fin.ext
    omega

/-- 概要：零次パラメータの切断は単体集合の射に関して自然。
方針：積の二つの成分を定義で計算する。
規約：区間ではなく零次パラメータ。
使われ方：Goerss–Jardine I §7。評価写像の基点保存。 -/
@[reassoc]
theorem zeroSection_natural {X Y : SSet.{u}} (f : X ⟶ Y) :
    f ≫ zeroSection Y = zeroSection X ≫ f ▷ (Δ[0] : SSet.{u}) := rfl

/-- 概要：点つき射の定数な零次パラメータ族を内部 Hom へ移す。
方針：零次パラメータを捨ててから元の射を施し、相対 curry を取る。
規約：頂点の標準代表となる Δ[0] からの射。
使われ方：Goerss–Jardine I §7。写像空間の端点の表示。 -/
def pointFamily {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    (Δ[0] : SSet.{u}) ⟶ (PointedObject.basedHom X Y).right :=
  _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry X Y (fst X.right (Δ[0] : SSet.{u}) ≫ f.right) (by
    rw [whiskerRight_fst_assoc, Under.w f]
    rfl)

/-- 概要：点つき射が表す内部 Hom の頂点。
方針：pointFamily を Yoneda で零単体へ移す。
規約：パラメータ族の curry による表示を使う。
使われ方：Goerss–Jardine I §7。球面からの射の連結成分。 -/
def familyVertex {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    (PointedObject.basedHom X Y).right _⦋0⦌ := SSet.yonedaEquiv (pointFamily f)

/-- 概要：内部 Hom の頂点を評価して点つき射へ戻す。
方針：Yoneda の逆を uncurry し、零次パラメータの切断で評価する。
規約：基点保存は内部 Hom の等化子条件から得る。
使われ方：Goerss–Jardine I §7。写像空間の頂点からの実際の射。 -/
def familyMap (X Y : PointedSimplicialSet.{u})
    (v : (PointedObject.basedHom X Y).right _⦋0⦌) : X ⟶ Y :=
  Under.homMk (zeroSection X.right ≫
    MonoidalClosed.uncurry (SSet.yonedaEquiv.symm v ≫ PointedObject.basedHomι X Y)) (by
      rw [← Category.assoc, zeroSection_natural, Category.assoc, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.uncurry_basepoint,
        comp_toUnit_assoc]
      rfl)

/-- 概要：パラメータ族で頂点へ移した点つき射を戻すと元の射。
方針：Yoneda、curry、零次パラメータの切断の順に逆関係を使う。
規約：通常の点つき射の等式。
使われ方：Goerss–Jardine I §7。頂点表示の左逆。 -/
@[simp]
theorem familyMap_familyVertex {X Y : PointedSimplicialSet.{u}} (f : X ⟶ Y) :
    familyMap X Y (familyVertex f) = f := by
  apply Under.UnderMorphism.ext
  change zeroSection X.right ≫ MonoidalClosed.uncurry
    (SSet.yonedaEquiv.symm (SSet.yonedaEquiv (pointFamily f)) ≫ PointedObject.basedHomι X Y) = _
  rw [Equiv.symm_apply_apply]
  change zeroSection X.right ≫ MonoidalClosed.uncurry
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry X Y (fst X.right (Δ[0] : SSet.{u}) ≫ f.right) _ ≫ PointedObject.basedHomι X Y) = _
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι, MonoidalClosed.uncurry_curry, ← Category.assoc, zeroSection_fst,
    Category.id_comp]

/-- 概要：内部 Hom の頂点を射へ戻してから頂点へ移すと元の頂点。
方針：包含後で curry の等式へ移し、零次パラメータの射影と切断を消す。
規約：標的の Kan 性は不要。
使われ方：Goerss–Jardine I §7。頂点表示の右逆。 -/
@[simp]
theorem familyVertex_familyMap (X Y : PointedSimplicialSet.{u})
    (v : (PointedObject.basedHom X Y).right _⦋0⦌) : familyVertex (familyMap X Y v) = v := by
  apply SSet.yonedaEquiv.symm.injective
  change SSet.yonedaEquiv.symm (SSet.yonedaEquiv (pointFamily (familyMap X Y v))) = _
  rw [Equiv.symm_apply_apply]
  apply (cancel_mono (PointedObject.basedHomι X Y)).1
  change _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry X Y _ _ ≫ PointedObject.basedHomι X Y = _
  rw [_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι]
  change MonoidalClosed.curry (fst X.right (Δ[0] : SSet.{u}) ≫
    (zeroSection X.right ≫ MonoidalClosed.uncurry
      (SSet.yonedaEquiv.symm v ≫ PointedObject.basedHomι X Y))) = _
  rw [← Category.assoc, fst_zeroSection, Category.id_comp, MonoidalClosed.curry_uncurry]

/-- 概要：パラメータ付き curry による点つき射と内部 Hom の頂点の同値。
方針：評価と定数な零次パラメータ族が互いに逆であることを使う。
規約：通常の単体集合の指数と等化子の定義だけを用いる。
使われ方：Goerss–Jardine I §7、Kerodon §3.2.2（Tag 00VJ）。球面の写像空間の π₀ の比較。 -/
def familyVertexEquiv (X Y : PointedSimplicialSet.{u}) :
    (X ⟶ Y) ≃ (PointedObject.basedHom X Y).right _⦋0⦌ where
  toFun := familyVertex
  invFun := familyMap X Y
  left_inv := familyMap_familyVertex
  right_inv := familyVertex_familyMap X Y

/-- 概要：パラメータ族の頂点表示は点つき射の後合成と可換。
方針：包含後で curry の標的の自然性を使う。
規約：標的の Kan 性は不要。
使われ方：Goerss–Jardine I §7。球面の成分比較の標的に関する自然性。 -/
theorem familyVertex_post {A X Y : PointedSimplicialSet.{u}} (f : A ⟶ X) (p : X ⟶ Y) :
    (PointedObject.basedHomMap A p).right.app _ (familyVertex f) = familyVertex (f ≫ p) := by
  have hm : pointFamily f ≫ (PointedObject.basedHomMap A p).right = pointFamily (f ≫ p) := by
    apply (cancel_mono (PointedObject.basedHomι A Y)).1
    rw [Category.assoc, PointedObject.basedHomMap_ι, ← Category.assoc]
    simp only [pointFamily, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι]
    rw [← MonoidalClosed.curry_natural_right]
    rfl
  change (PointedObject.basedHomMap A p).right.app _ (SSet.yonedaEquiv (pointFamily f)) = _
  rw [← SSet.yonedaEquiv_comp]
  exact congrArg SSet.yonedaEquiv hm

/-- 概要：パラメータ族の頂点表示は点つき射の前合成と可換。
方針：内部 Hom の制限を包含し、curry の源の自然性を使う。
規約：源の射に単射性を仮定しない。
使われ方：Goerss–Jardine I §7。円の自己射による前合成の成分計算。 -/
theorem familyVertex_pre {A B Y : PointedSimplicialSet.{u}} (i : A ⟶ B) (f : B ⟶ Y) :
    (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y).right.app _ (familyVertex f) = familyVertex (i ≫ f) := by
  have hm : pointFamily f ≫ (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y).right = pointFamily (i ≫ f) := by
    apply (cancel_mono (PointedObject.basedHomι A Y)).1
    rw [Category.assoc]
    change pointFamily f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre i Y ≫ PointedObject.basedHomι A Y) = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.pre_ι, ← Category.assoc]
    simp only [pointFamily, _root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.paramCurry_ι]
    rw [MonoidalClosed.curry_pre_app, whiskerRight_fst_assoc]
    rfl
  change (_root_.SerrePositivity.InfinityCategories.HTT.PointedSimplicialSets.prePointed i Y).right.app _ (SSet.yonedaEquiv (pointFamily f)) = _
  rw [← SSet.yonedaEquiv_comp]
  exact congrArg SSet.yonedaEquiv hm

end

end SerrePositivity.KST.Spectra.PointedMapping
