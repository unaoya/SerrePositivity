module
public import SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentPathImageEndpoints
public import SerrePositivity.KST.SConstruction.CoherentStringDiagramCells
public import SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.HomMono

/-! # 元の合成列の端点を固定する native Hom の評価
概要：各合成列の元の Path の全作用を、元の射の両端を持つ同じ写像空間へ写す。
方針：元の頂点の等式だけを移し、精密化の全豊穣作用との厳密な可換性を証明する。
規約：局所 Kan 性や新しい円柱の存在を仮定せず、元の作用そのものを使う。
使われ方：高次精密化の Path 単体を、一つの native Hom に値を取る全族へ束ねる。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SimplicialThickening SSet
open SerrePositivity.InfinityCategories
open scoped _root_.Simplicial
variable {I : Type u} [SmallCategory I] {C : Type v} [Category.{u} C] [SimplicialCategory C]
  {x y : I} {f : x ⟶ y}

/-- 元の合成列の両端を、指定した元の射の両端に厳密に合わせた全 Path 評価。 -/
def coherentStringNativeMap
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) :
    nerve (Path (ULift.up 0 : ULift.{u} (Fin (s.length + 1))) (ULift.up (Fin.last s.length))) ⟶
      SimplicialCategory.sHom (coherentStringVertexObject Q x) (coherentStringVertexObject Q y) :=
  (coherentStringDiagramCell Q s.chain).map (.mk (ULift.up 0))
      (.mk (ULift.up (Fin.last s.length))) ≫ eqToHom (by
    change SimplicialCategory.sHom (coherentStringVertexObject Q (s.chain.obj 0))
      (coherentStringVertexObject Q (s.chain.obj (Fin.last s.length))) = _
    rw [_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_first, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_last])

/-- 端点の表示を移しても、元の合成列の豊穣作用そのものである。 -/
lemma coherentStringNativeMap_heq
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    (s : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f) :
    HEq (coherentStringNativeMap Q s)
      ((coherentStringDiagramCell Q s.chain).map (.mk (ULift.up 0))
        (.mk (ULift.up (Fin.last s.length)))) :=
  comp_eqToHom_heq _ _

/-- 豊穣作用の評価は、同じ元の対象の別表示で依存等号として一致する。 -/
lemma coherentString_enrichedMap_objects_heq {A : Type w} [EnrichedCategory SSet.{u} A]
    (F : EnrichedFunctor SSet.{u} A C) {a b a' b' : A} (ha : a = a') (hb : b = b') :
    HEq (F.map a b) (F.map a' b') := by
  subst a'
  subst b'
  rfl

/-- 元の全 Path 評価は、両端固定の全精密化と厳密に可換。 -/
lemma coherentStringNativeMap_naturality
    (Q : (SSet.uliftFunctor.{v, u}).obj (nerve I) ⟶ SimplicialNerve C)
    {s t : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.CoherentArrowString f} (a : s ⟶ t) :
    nerveMap (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathReindexFunctor a) ≫ coherentStringNativeMap Q t =
      coherentStringNativeMap Q s := by
  have hc := coherentStringDiagramCell_naturality Q t.chain a.map
  rw [a.comm] at hc
  have hm := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.SimplicialCategories.enrichedFunctor_map_heq hc (.mk (ULift.up 0))
    (.mk (ULift.up (Fin.last s.length)))
  have ha₀ : (SimplicialThickening.mk (ULift.up (a.map.toOrderHom 0)) :
      SimplicialThickening (ULift.{u} (Fin (t.length + 1)))) = .mk (ULift.up 0) :=
    congrArg (fun i => SimplicialThickening.mk (ULift.up i)) a.first
  have ha₁ : (SimplicialThickening.mk (ULift.up (a.map.toOrderHom (Fin.last s.length))) :
      SimplicialThickening (ULift.{u} (Fin (t.length + 1)))) =
        .mk (ULift.up (Fin.last t.length)) :=
    congrArg (fun i => SimplicialThickening.mk (ULift.up i)) a.last
  have hg := (coherentStringNativeMap_heq Q t).trans
    (coherentString_enrichedMap_objects_heq (coherentStringDiagramCell Q t.chain)
      ha₀ ha₁).symm
  have hp : nerve (Path (ULift.up 0 : ULift.{u} (Fin (t.length + 1)))
      (ULift.up (Fin.last t.length))) =
    nerve (Path (ULift.up (a.map.toOrderHom 0) : ULift.{u} (Fin (t.length + 1)))
      (ULift.up (a.map.toOrderHom (Fin.last s.length)))) := by
    rw [a.first, a.last]
  have he : SimplicialCategory.sHom (coherentStringVertexObject Q x)
      (coherentStringVertexObject Q y) =
    SimplicialCategory.sHom
      ((coherentStringDiagramCell Q t.chain).obj (.mk (ULift.up (a.map.toOrderHom 0))))
      ((coherentStringDiagramCell Q t.chain).obj
        (.mk (ULift.up (a.map.toOrderHom (Fin.last s.length))))) := by
    change _ = SimplicialCategory.sHom
      (coherentStringVertexObject Q (t.chain.obj (a.map.toOrderHom 0)))
      (coherentStringVertexObject Q (t.chain.obj (a.map.toOrderHom (Fin.last s.length))))
    rw [a.first, a.last, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_first, _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentArrowString_last]
  apply eq_of_heq
  exact (heq_comp rfl hp he (_root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.coherentStringPathReindexFunctor_native_heq a) hg).trans
    (hm.trans (coherentStringNativeMap_heq Q s).symm)

end SerrePositivity.KST.SConstruction
