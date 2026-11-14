module
public import SerrePositivity.DifferentialGraded.Presentation.GeneratedHom.SphereLifts
public import SerrePositivity.DifferentialGraded.Presentation.Category




public import SerrePositivity.InfinityCategories.Project.DerivedCategories.CompactnessAndPresentability.DGKappaPresentedFreeCoproduct
/-!
概要：κ 未満個の異なる出発提示を一つの小さい dg 圏提示へまとめる。
方針：異成分の Hom を零にした非連結和を、保持した ordinal 同値で再添字する。
規約：seed や標的 dg 圏を選択に含めず、指定した平坦化ラベルを保持する。
使われ方：異なる code・arrow の直和と cone に必要な同時精密化の出発圏。
-/
@[expose] public section
noncomputable section
universe u v
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory DifferentialGraded
variable (R : Type u) [CommRing R] (κ : Cardinal.{u}) {J : Type u}
  (c : J → DGCategoryPresentationCode R κ)

/-- 対象をまだ ordinal へ戻さない非連結和の提示データ。 -/
def dgKappaSourceCodeSigmaData :
    DGCategoryPresentationData R κ.ord.ToType (Σ j, (c j).Objects R κ) :=
  DGCategoryPresentationData.sigma R κ.ord.ToType J
    (fun j => (c j).Objects R κ) (fun j => (c j).toData R κ)

/-- 指定した対象平坦化により小さい元のコード型へ戻した非連結和。 -/
def dgKappaSourceCodeCoproduct
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaFreeSumShape (fun j => (c j).ordinal)) : DGCategoryPresentationCode R κ :=
  DGCategoryPresentationData.reindex R κ _ (dgKappaSourceCodeSigmaData R κ c)
    s.ordinal s.reindex

/-- κ 正則かつ添字数が κ 未満なら、同じコード型に非連結和を収容できる。 -/
lemma dgKappaSourceCodeCoproductShape_nonempty (hreg : κ.IsRegular)
    (hJ : Cardinal.mk J < κ) :
    Nonempty (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaFreeSumShape (fun j => (c j).ordinal)) :=
  _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgKappaFreeSumShape_nonempty _ hreg hJ

/-- 全 Hom が同型で、対象について全射となる再添字評価。 -/
def dgKappaSourceCodeCoproductEvaluation
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaFreeSumShape (fun j => (c j).ordinal)) :
    letI := (dgKappaSourceCodeSigmaData R κ c).enrichment R κ.ord.ToType _
    DGFunctor R ((dgKappaSourceCodeCoproduct R κ c s).Objects R κ)
      (Σ j, (c j).Objects R κ) :=
  DGCategoryPresentationData.reindexEvaluation R κ _ (dgKappaSourceCodeSigmaData R κ c)
    s.ordinal s.reindex

/-- 各成分の元の提示から、再添字済み共通提示への dg 包含。 -/
def dgKappaSourceCodeCoproductInclusion
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaFreeSumShape (fun j => (c j).ordinal)) (j : J) :
    DGFunctor R ((c j).Objects R κ) ((dgKappaSourceCodeCoproduct R κ c s).Objects R κ) := by
  letI := (dgKappaSourceCodeSigmaData R κ c).enrichment R κ.ord.ToType _
  exact (DGCategoryPresentationData.sigmaInclusion R κ.ord.ToType J
    (fun j => (c j).Objects R κ) (fun j => (c j).toData R κ) j).comp
    (DGCategoryPresentationData.reindexInverse R κ _ (dgKappaSourceCodeSigmaData R κ c)
      s.ordinal s.reindex)

/-- 各成分の関手を保持して共通提示から任意の標的へ評価する。 -/
def dgKappaSourceCodeCoproductDesc
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaFreeSumShape (fun j => (c j).ordinal)) (D : Type v) [DGCategory R D]
    (F : ∀ j, DGFunctor R ((c j).Objects R κ) D) :
    DGFunctor R ((dgKappaSourceCodeCoproduct R κ c s).Objects R κ) D := by
  letI := (dgKappaSourceCodeSigmaData R κ c).enrichment R κ.ord.ToType _
  exact (dgKappaSourceCodeCoproductEvaluation R κ c s).comp
    (DGCategoryPresentationData.sigmaDesc R κ.ord.ToType J
      (fun j => (c j).Objects R κ) (fun j => (c j).toData R κ) D F)

lemma dgKappaSourceCodeCoproductInclusion_obj
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaFreeSumShape (fun j => (c j).ordinal)) (j : J)
    (x : (c j).Objects R κ) :
    (dgKappaSourceCodeCoproductInclusion R κ c s j).obj x = s.reindex.symm ⟨j, x⟩ := rfl

lemma dgKappaSourceCodeCoproductDesc_inclusion_obj
    (s : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.DGKappaFreeSumShape (fun j => (c j).ordinal)) (D : Type v) [DGCategory R D]
    (F : ∀ j, DGFunctor R ((c j).Objects R κ) D) (j : J) (x : (c j).Objects R κ) :
    (dgKappaSourceCodeCoproductDesc R κ c s D F).obj
      ((dgKappaSourceCodeCoproductInclusion R κ c s j).obj x) = (F j).obj x := by
  change (fun p : Σ j, (c j).Objects R κ => (F p.1).obj p.2)
    (s.reindex (s.reindex.symm ⟨j, x⟩)) = _
  rw [s.reindex.apply_symm_apply]

end SerrePositivity.InfinityCategories.Project.DerivedCategories
