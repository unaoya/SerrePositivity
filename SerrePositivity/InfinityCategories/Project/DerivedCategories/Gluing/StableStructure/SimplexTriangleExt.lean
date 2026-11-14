module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.StableStructure.ClosedAugmentationTriangleFaces

/-! # 三辺と高次係数による dg 三角形の比較

概要：三つの面と三点係数の一致から、実 dg 二単体全体の一致を得る。
方針：単射面制限から辺係数を回収し、全成分の外延性へ渡す。
規約：頂点の指定を保ち、辺の一致だけで高次係数を同一視しない。
使われ方：標準正規化側面の単位退化を実単体の等式として証明する。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
open CategoryTheory DifferentialGraded
universe u v
private lemma dgGluingTriangleExt (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 2) (hobj : s.obj = t.obj)
    (h01 : HEq (s.edgeHom 0 1 (by decide)) (t.edgeHom 0 1 (by decide)))
    (h02 : HEq (s.edgeHom 0 2 (by decide)) (t.edgeHom 0 2 (by decide)))
    (h12 : HEq (s.edgeHom 1 2 (by decide)) (t.edgeHom 1 2 (by decide)))
    (h012 : HEq s.triangleHom t.triangleHom) : s = t := by
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.ext
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.SimplexData.ext hobj
  apply Function.hfunext rfl
  intro I I' h
  cases h
  apply Function.hfunext rfl
  intro a a' h
  cases h
  apply Function.hfunext rfl
  intro b b' h
  cases h
  apply Function.hfunext rfl
  intro k k' h
  cases h
  apply Function.hfunext rfl
  intro hI hI' h
  cases h
  apply Function.hfunext rfl
  intro ha ha' h
  cases h
  apply Function.hfunext rfl
  intro hb hb' h
  cases h
  apply Function.hfunext rfl
  intro hk hk' h
  cases h
  fin_cases I
  all_goals norm_num at hI
  all_goals fin_cases a
  all_goals norm_num at ha
  all_goals fin_cases b
  all_goals norm_num at hb
  all_goals first
    | exact False.elim ((of_decide_eq_false rfl) ha)
    | exact False.elim ((of_decide_eq_false rfl) hb)
    | skip
  all_goals subst k
  all_goals first | exact h01 | exact h02 | exact h12 | exact h012


private lemma dgGluingTriangleFaceEdge (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 2) (i : Fin 3)
    (h : s.pullback (SimplexCategory.δ i).toOrderHom =
      t.pullback (SimplexCategory.δ i).toOrderHom) :
    HEq (s.edgeHom (i.succAbove 0) (i.succAbove 1)
      ((Fin.succAboveOrderEmb i).strictMono (by decide)))
      (t.edgeHom (i.succAbove 0) (i.succAbove 1)
      ((Fin.succAboveOrderEmb i).strictMono (by decide))) := by
  let α := (SimplexCategory.δ i).toOrderHom
  have hs := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq s.toSimplexData
    (t.pullback α).toSimplexData α (Fin.succAboveOrderEmb i).injective
    (congrArg _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.toSimplexData h) 0 1 (by decide)
    ((Fin.succAboveOrderEmb i).strictMono (by decide))
  have ht := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.edgeHom_heq_of_pullback_eq t.toSimplexData
    (t.pullback α).toSimplexData α (Fin.succAboveOrderEmb i).injective
    rfl 0 1 (by decide) ((Fin.succAboveOrderEmb i).strictMono (by decide))
  exact hs.trans ht.symm

lemma dgGluingTriangle_faces_ext (R : Type u) [CommRing R] (E : Type v) [_root_.SerrePositivity.DifferentialGraded.DGCategory R E]
    (s t : _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex R E 2) (hobj : s.obj = t.obj)
    (hface : ∀ i : Fin 3, s.pullback (SimplexCategory.δ i).toOrderHom =
      t.pullback (SimplexCategory.δ i).toOrderHom)
    (hhigh : HEq s.triangleHom t.triangleHom) : s=t := by
  exact dgGluingTriangleExt R E s t hobj (dgGluingTriangleFaceEdge R E s t 2 (hface 2))
    (dgGluingTriangleFaceEdge R E s t 1 (hface 1))
    (dgGluingTriangleFaceEdge R E s t 0 (hface 0)) hhigh
end SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing
