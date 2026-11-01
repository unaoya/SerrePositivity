module

public import SerrePositivity.InfinityCategories.F1B.MappingSpaces.PinchedComposition
public import SerrePositivity.InfinityCategories.F1B.PinchedFamilyHomotopy

/-!
概要：可逆な端点成分による実 pinched Hom の coherent な輸送を構成する。
方針：既存の前後合成作用の結合・単位二胞体から実際の逆を作る。
規約：端点の等式や相対的な厳密化を入力しない。
使われ方：指定局所化の比較二胞体による元の Hom 族の輸送。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.EInfinity.FrameHom
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {D : SSet.{u}} [Quasicategory D]

/-- 概要：可逆な源成分の前合成は実 pinched Hom の QCat 同値。
方針：逆成分で逆写像を作り、既存の結合・単位二胞体を使う。
規約：元の前合成作用を順射に保つ。使われ方：比較二胞体の源成分の輸送。 -/
def pinchedPrecomposeEquivalence {x x' : D _⦋0⦌} (y : D _⦋0⦌)
    (e : HomotopyCategory.mk x ≅ HomotopyCategory.mk x') :
    QCatEquivalence (pinchedHom x y) (pinchedHom x' y) where
  hom := PinchedInterval.precompose y e.inv
  inv := PinchedInterval.precompose y e.hom
  homInvIso := by
    have h := PinchedInterval.precomposeCompIso y e.hom e.inv
    simp only [Iso.hom_inv_id] at h
    exact h ≪≫ PinchedInterval.precomposeIdIso x y
  invHomIso := by
    have h := PinchedInterval.precomposeCompIso y e.inv e.hom
    simp only [Iso.inv_hom_id] at h
    exact h ≪≫ PinchedInterval.precomposeIdIso x' y

/-- 概要：可逆な標的成分の後合成は実 pinched Hom の QCat 同値。
方針：逆成分で逆写像を作り、既存の結合・単位二胞体を使う。
規約：元の後合成作用を順射に保つ。使われ方：比較二胞体の標的成分の輸送。 -/
def pinchedPostcomposeEquivalence (x : D _⦋0⦌) {y y' : D _⦋0⦌}
    (e : HomotopyCategory.mk y ≅ HomotopyCategory.mk y') :
    QCatEquivalence (pinchedHom x y) (pinchedHom x y') where
  hom := PinchedInterval.postcompose x e.hom
  inv := PinchedInterval.postcompose x e.inv
  homInvIso := by
    have h := PinchedInterval.postcomposeCompIso x e.hom e.inv
    simp only [Iso.hom_inv_id] at h
    exact h ≪≫ PinchedInterval.postcomposeIdIso x y
  invHomIso := by
    have h := PinchedInterval.postcomposeCompIso x e.inv e.hom
    simp only [Iso.inv_hom_id] at h
    exact h ≪≫ PinchedInterval.postcomposeIdIso x y'

/-- 概要：指定された二つの可逆成分で pinched Hom の両端を輸送する。
方針：源の逆成分による前合成と標的成分による後合成を合成する。
規約：同値とその二胞体をデータとして返す。使われ方：指定局所化への Hom 比較。 -/
def pinchedEndpointEquivalence {x y x' y' : D _⦋0⦌}
    (ex : HomotopyCategory.mk x ≅ HomotopyCategory.mk x')
    (ey : HomotopyCategory.mk y ≅ HomotopyCategory.mk y') :
    QCatEquivalence (pinchedHom x y) (pinchedHom x' y') :=
  (pinchedPrecomposeEquivalence y ex).trans (pinchedPostcomposeEquivalence x' ey)

/-- 概要：源成分の輸送は任意のパラメータ族で元の前合成を表す。
方針：区間模型との比較二胞体を同じ族に前合成する。
規約：パラメータに充填性を要求しない。使われ方：零単体と全図式の照合。 -/
lemma pinchedPrecomposeEquivalence_family {T : SSet.{u}} {x x' y : D _⦋0⦌}
    (e : HomotopyCategory.mk x ≅ HomotopyCategory.mk x') (f : T ⟶ pinchedHom x y) :
    intervalFamilyHom ((f ≫ (pinchedPrecomposeEquivalence y e).hom) ≫
      pinchedHomToIntervalMappingSpace x' y) =
      constantFunctorHomMap T e.inv ≫
        intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace x y) := by
  change intervalFamilyHom ((f ≫ PinchedInterval.liftMap (intervalPrecompose y e.inv)) ≫
    pinchedHomToIntervalMappingSpace x' y) = _
  have H : FunctorIso
      ((f ≫ PinchedInterval.liftMap (intervalPrecompose y e.inv)) ≫
        pinchedHomToIntervalMappingSpace x' y)
      ((f ≫ pinchedHomToIntervalMappingSpace x y) ≫ intervalPrecompose y e.inv) := by
    simpa only [Category.assoc] using
      FunctorIso.precomp (PinchedInterval.liftMapComparisonIso (intervalPrecompose y e.inv)) f
  have h := intervalFamilyHom_eq_of_homotopy H.simplicialHomotopy
  exact h.trans (intervalPrecompose_family e.inv _)

/-- 概要：標的成分の輸送は任意のパラメータ族で元の後合成を表す。
方針：区間模型との比較二胞体を同じ族に前合成する。
規約：パラメータに充填性を要求しない。使われ方：零単体と全図式の照合。 -/
lemma pinchedPostcomposeEquivalence_family {T : SSet.{u}} {x y y' : D _⦋0⦌}
    (e : HomotopyCategory.mk y ≅ HomotopyCategory.mk y') (f : T ⟶ pinchedHom x y) :
    intervalFamilyHom ((f ≫ (pinchedPostcomposeEquivalence x e).hom) ≫
      pinchedHomToIntervalMappingSpace x y') =
      intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace x y) ≫
        constantFunctorHomMap T e.hom := by
  change intervalFamilyHom ((f ≫ PinchedInterval.liftMap (intervalPostcompose x e.hom)) ≫
    pinchedHomToIntervalMappingSpace x y') = _
  have H : FunctorIso
      ((f ≫ PinchedInterval.liftMap (intervalPostcompose x e.hom)) ≫
        pinchedHomToIntervalMappingSpace x y')
      ((f ≫ pinchedHomToIntervalMappingSpace x y) ≫ intervalPostcompose x e.hom) := by
    simpa only [Category.assoc] using
      FunctorIso.precomp (PinchedInterval.liftMapComparisonIso (intervalPostcompose x e.hom)) f
  have h := intervalFamilyHom_eq_of_homotopy H.simplicialHomotopy
  exact h.trans (intervalPostcompose_family e.hom _)

/-- 概要：両端の輸送は同じ指定成分による共役を全族で表す。
方針：前後合成の二つの族公式を合成する。
規約：任意の単体集合をパラメータに持つ。使われ方：局所化三角形の coherent な整合。 -/
lemma pinchedEndpointEquivalence_family {T : SSet.{u}} {x y x' y' : D _⦋0⦌}
    (ex : HomotopyCategory.mk x ≅ HomotopyCategory.mk x')
    (ey : HomotopyCategory.mk y ≅ HomotopyCategory.mk y') (f : T ⟶ pinchedHom x y) :
    intervalFamilyHom ((f ≫ (pinchedEndpointEquivalence ex ey).hom) ≫
      pinchedHomToIntervalMappingSpace x' y') =
      constantFunctorHomMap T ex.inv ≫
        intervalFamilyHom (f ≫ pinchedHomToIntervalMappingSpace x y) ≫
          constantFunctorHomMap T ey.hom := by
  change intervalFamilyHom (((f ≫ (pinchedPrecomposeEquivalence y ex).hom) ≫
    (pinchedPostcomposeEquivalence x' ey).hom) ≫ _) = _
  rw [pinchedPostcomposeEquivalence_family, pinchedPrecomposeEquivalence_family, Category.assoc]

end SerrePositivity.EInfinity.FrameHom
