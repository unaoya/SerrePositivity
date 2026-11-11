module
public import SerrePositivity.KST.SConstruction.CoherentCutSpanFamilies
public import SerrePositivity.KST.SConstruction.KPrismPathDecoding
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.MapSmallness

/-! # 元の K prism の Kan な終点での二切断族の相対合成
概要：元の prism の終点が上段にある場合、二切断円柱の相対合成を追加の Kan 仮定なしで作る。
方針：元の縦辺から上段の対象を回収し、基点固定写像空間の Kan 性を使う。
規約：全点つき対象の nerve の Kan 性を要求せず、同じ終点の写像空間だけを使う。
使われ方：元の K の高次 prism から指定境界を保つ実写像族への接続。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening MonoidalCategory SSet
open Spectra SerrePositivity.InfinityCategories
open scoped Simplicial
local instance kPrismCutSpanFamilies_pointed_simplicialCategory :
    SimplicialCategory PointedSimplicialSet.{u} := PointedEnrichment.simplicialCategory

/-- 元の prism の各上端頂点は、元の次段の点つき Kan 対象そのもの。 -/
lemma kKanOriginalPrism_top_object {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n : ℕ} (s : (nerve I) _⦋n⦌)
    (a : (Δ[n] : SSet.{u + 1}) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject ((kKanOriginalSuspensionPrism r F s).app (Opposite.op ⦋0⦌)
      (a, SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) =
      ((kKanSequence (F.obj (s.obj (a 0)))).level (r + 1)).space := by
  have h := congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject (ConcreteCategory.congr_hom
    (NatTrans.congr_app (kKanOriginalSuspensionPrism_vertex r F s a)
      (Opposite.op ⦋0⦌)) (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)))
  have he : (SSet.yonedaEquiv.symm
      (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((kKanSequence (F.obj (s.obj (a 0)))).sigma r)).edge).app
      (Opposite.op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveVertex ((kKanSequence (F.obj (s.obj (a 0)))).level (r + 1)).space := by
    have ht : SSet.stdSimplex.objEquiv
        (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2) :
          (Δ[1] : SSet.{u + 1}) _⦋0⦌) = SimplexCategory.δ (0 : Fin 2) := by
      ext t
      fin_cases t
      rfl
    rw [SSet.yonedaEquiv_symm_app, ht]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveEdge ((kKanSequence (F.obj (s.obj (a 0)))).sigma r)).tgt_eq
  have hc : (SSet.const a : (Δ[1] : SSet.{u + 1}) ⟶ Δ[n]).app
      (Opposite.op ⦋0⦌) (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)) = a := by
    simp only [SSet.const_app, SimplexCategory.const_eq_id, op_id,
      CategoryTheory.Functor.map_id_apply]
    rfl
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject ((kKanOriginalSuspensionPrism r F s).app _
    ((SSet.const a).app _ (SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2)),
      SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2))) = _ at h
  rw [hc] at h
  exact h.trans (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject he)

/-- 元の prism の高次単体の上段にある頂点は、元の Kan 段の対象を回収する。 -/
lemma kKanPrism_top_simplex_object {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n m : ℕ} (s : (nerve I) _⦋n⦌)
    (p : ((Δ[n] : SSet.{u + 1}) ⊗ Δ[1]) _⦋m⦌) (k : Fin (m + 1))
    (hp : p.2 k = 1) :
    ((kKanOriginalSuspensionPrism r F s).app _ p).obj (.mk (ULift.up k)) =
      ((kKanSequence (F.obj (s.obj (p.1 k)))).level (r + 1)).space := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentMap_simplex_obj]
  let θ := SimplexCategory.const ⦋0⦌ ⦋m⦌ k
  have ht : (Δ[1] : SSet.{u + 1}).map θ.op p.2 =
      SSet.stdSimplex.obj₀Equiv.symm (1 : Fin 2) := by
    apply SSet.stdSimplex.ext
    intro t
    fin_cases t
    exact hp
  change _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.coherentNerveObject ((kKanOriginalSuspensionPrism r F s).app _
    ((Δ[n] : SSet.{u + 1}).map θ.op p.1, (Δ[1] : SSet.{u + 1}).map θ.op p.2)) = _
  rw [ht, kKanOriginalPrism_top_object]
  rfl

/-- Kan 性は元の上段の対象から導き、写像空間の Kan 性を追加仮定にしない。 -/
lemma kKanPrism_top_hom_kanComplex {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n m : ℕ} (s : (nerve I) _⦋n⦌)
    (p : ((Δ[n] : SSet.{u + 1}) ⊗ Δ[1]) _⦋m⦌) (i k : Fin (m + 1))
    (hp : p.2 k = 1) :
    KanComplex (SimplicialCategory.sHom
      (((kKanOriginalSuspensionPrism r F s).app _ p).obj (.mk (ULift.up i)))
      (((kKanOriginalSuspensionPrism r F s).app _ p).obj (.mk (ULift.up k)))) := by
  let : KanComplex
      ((((kKanOriginalSuspensionPrism r F s).app _ p).obj (.mk (ULift.up k))).right) := by
    rw [kKanPrism_top_simplex_object r F s p k hp]
    infer_instance
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.PointedMapping.basedHom_kanComplex _ _

/-- 上段で終わる元の高次 prism の二切断円柱を、元の共通合成面を固定して合成する。 -/
def kKanPrismCutSpanComposite {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n m : ℕ} (s : (nerve I) _⦋n⦌)
    (p : ((Δ[n] : SSet.{u + 1}) ⊗ Δ[1]) _⦋m⦌) (i j k l : Fin (m + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hil : i ≤ l) (hlk : l ≤ k) (hp : p.2 k = 1) :=
  letI := kKanPrism_top_hom_kanComplex r F s p i k hp
  coherentCutSpanComposite ((kKanOriginalSuspensionPrism r F s).app _ p)
    (show (ULift.up i : ULift.{u} _) ≤ ULift.up j from hij)
    (show (ULift.up j : ULift.{u} _) ≤ ULift.up k from hjk)
    (show (ULift.up i : ULift.{u} _) ≤ ULift.up l from hil)
    (show (ULift.up l : ULift.{u} _) ≤ ULift.up k from hlk)

/-- 元の K prism の二切断の相対合成は、共通面で元の豊穣作用を全時刻に保つ。 -/
lemma kKanPrismCutSpanComposite_relative {I : Type u} [SmallCategory I]
    (r : ℕ) (F : I ⥤ StableModel.{u}) {n m : ℕ} (s : (nerve I) _⦋n⦌)
    (p : ((Δ[n] : SSet.{u + 1}) ⊗ Δ[1]) _⦋m⦌) (i j k l : Fin (m + 1))
    (hij : i ≤ j) (hjk : j ≤ k) (hil : i ≤ l) (hlk : l ≤ k) (hp : p.2 k = 1) :
    let B := coherentDoubleCutBoundary (ULift.up i : ULift.{u} _) (ULift.up j)
      (ULift.up k) (ULift.up l)
    (B.ι ▷ (Δ[1] : SSet.{u})) ≫
        (kKanPrismCutSpanComposite r F s p i j k l hij hjk hil hlk hp).h =
      CartesianMonoidalCategory.fst (B : SSet.{u}) Δ[1] ≫ B.ι ≫
        coherentDiagramPathFamily (kKanOriginalSuspensionPrism r F s) p i k := by
  let := kKanPrism_top_hom_kanComplex r F s p i k hp
  exact coherentCutSpanComposite_relative_original
    ((kKanOriginalSuspensionPrism r F s).app _ p) hij hjk hil hlk

end SerrePositivity.KST.SConstruction
