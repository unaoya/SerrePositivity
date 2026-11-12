module

public import SerrePositivity.KST.Spectra.CosimplicialKanReplacement
public import SerrePositivity.Spectra.PointedSimplicialSet.Basic

/-!
概要：点つき余単体単体集合の Reedy Kan 置換。
方針：忘却した図式を置換し、自然な単位で元の基点を移す。
規約：余単体射は基点を厳密に保存する。Kan 性は各値の基礎単体集合について述べる。
使われ方：Goerss–Jardine VII §4、HTT A.3.3。点つき Tot の具体的な係数の置換。
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits SSet

namespace SerrePositivity.KST.Spectra.PointedCosimplicialKanReplacement

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- 概要：各値の基点を Reedy 置換の自然な単位で移す。
方針：基点と置換の単位の合成を新しい基点とする。
規約：元の各値の Kan 性は不要。
使われ方：Goerss–Jardine VII §4。点つき Reedy 置換の対象。 -/
def obj (X : CosimplicialObject PointedSimplicialSet.{u}) :
    CosimplicialObject PointedSimplicialSet.{u} where
  obj j := Under.mk ((X.obj j).hom ≫
    (CosimplicialKanReplacement.unit.app (X ⋙ PointedSimplicialSet.forget)).app j)
  map {i j} f := Under.homMk
    ((CosimplicialKanReplacement.functor.obj (X ⋙ PointedSimplicialSet.forget)).map f)
    (by
      change ((X.obj i).hom ≫ _) ≫ _ = (X.obj j).hom ≫ _
      rw [Category.assoc, ← (CosimplicialKanReplacement.unit.app
        (X ⋙ PointedSimplicialSet.forget)).naturality f, ← Category.assoc]
      exact congrArg (fun t ↦ t ≫ _) (Under.w (X.map f)))
  map_id j := by
    apply Under.UnderMorphism.ext
    exact (CosimplicialKanReplacement.functor.obj
      (X ⋙ PointedSimplicialSet.forget)).map_id j
  map_comp f g := by
    apply Under.UnderMorphism.ext
    exact (CosimplicialKanReplacement.functor.obj
      (X ⋙ PointedSimplicialSet.forget)).map_comp f g

/-- 概要：点つき Reedy 置換への各段の標準比較。
方針：新しい基点を比較射の像として選んだ定義を使う。
規約：比較は厳密な余単体射。
使われ方：HTT A.3.3。置換前の点つき図式との比較。 -/
def unitApp (X : CosimplicialObject PointedSimplicialSet.{u}) : X ⟶ obj X where
  app j := Under.homMk
    ((CosimplicialKanReplacement.unit.app (X ⋙ PointedSimplicialSet.forget)).app j)
  naturality _ _ f := by
    apply Under.UnderMorphism.ext
    exact (CosimplicialKanReplacement.unit.app (X ⋙ PointedSimplicialSet.forget)).naturality f

/-- 概要：点つき Reedy 置換の各値は Kan 複体。
方針：忘却した Reedy 置換の Kan 性を使う。
規約：基点は Kan 条件を変えない。
使われ方：Goerss–Jardine VII §4。Tot の点つき Kan 係数。 -/
instance kanComplex (X : CosimplicialObject PointedSimplicialSet.{u}) (j : SimplexCategory) :
    KanComplex ((obj X).obj j).right :=
  CosimplicialKanReplacement.kanComplex (X ⋙ PointedSimplicialSet.forget) j

/-- 概要：点つき Reedy 置換の単位の各値は anodyne。
方針：基礎単体集合の比較射そのものを使う。
規約：元の各値の Kan 性は不要。
使われ方：Goerss–Jardine VII §4。点つき置換のホモトピー不変性。 -/
lemma unit_anodyne (X : CosimplicialObject PointedSimplicialSet.{u}) (j : SimplexCategory) :
    anodyneExtensions ((unitApp X).app j).right :=
  CosimplicialKanReplacement.unit_anodyne (X ⋙ PointedSimplicialSet.forget) j

/-- 概要：元の各値が Kan なら点つき Reedy 置換の単位は各段の全基点 π_* 同型。
方針：anodyne な比較射の Kan ホモトピー不変性を適用する。
規約：零次数の成分集合を含む全基点の主張。
使われ方：Goerss–Jardine VII §4。点つき Tot の係数の比較。 -/
lemma unit_piIsomorphism (X : CosimplicialObject PointedSimplicialSet.{u})
    [∀ j, KanComplex (X.obj j).right] (j : SimplexCategory) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (X := (X.obj j).right) (Y := ((obj X).obj j).right)
      ((unitApp X).app j).right :=
  kanPiIsomorphism_of_anodyne _ (unit_anodyne X j)

end

end SerrePositivity.KST.Spectra.PointedCosimplicialKanReplacement
