module

public import SerrePositivity.EInfinity.FrameHom.CoherentRightConeTransport
public import SerrePositivity.InfinityCategories.F1.Coherent.HomReindex

/-!
# 定値前面の元の coherent 錐と Hom 比較単体

概要：前面の全対象と全射が同じ恒等に正規化される錐を元の Hom 比較単体へ戻す。
方針：元の全頂点・全 Hom を端点の等号で正規化する。
規約：最後 Hom の全 path の式を保持する。
使われ方：native roof prism の一端。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v
namespace SerrePositivity.EInfinity.FrameHom.CoherentRightCone
open CategoryTheory SimplicialThickening SSet MonoidalCategory CartesianMonoidalCategory
open SerrePositivity.InfinityCategories
open scoped Simplicial
variable {C : Type v} [Category.{u} C] [SimplicialCategory C] {n : ℕ}
  (F : Fin (n + 1) ⥤ C) (Y : C)
  (L : ∀ i : Fin (n + 1),
    SimplicialCategory.sHom (vertex.{u} i.castSucc) (vertex (Fin.last (n + 1))) ⟶
      SimplicialCategory.sHom (F.obj i) Y)

lemma hom_cast_last_normalized (i : Fin (n + 1)) {X : C} (h : F.obj i = X) :
    hom F Y L i.castSucc (Fin.last (n + 1)) ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      ((obj_cast F Y i).trans h) (obj_last F Y)) =
    L i ≫ eqToHom (congrArg₂ SimplicialCategory.sHom h (rfl : Y = Y)) := by
  calc
    _ = (hom F Y L i.castSucc (Fin.last (n + 1)) ≫ eqToHom
        (congrArg₂ SimplicialCategory.sHom (obj_cast F Y i) (obj_last F Y))) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom h (rfl : Y = Y)) := by
      simp only [Category.assoc, eqToHom_trans]
    _ = _ := by rw [hom_cast_last]

lemma hom_cast_cast_normalized (i j : Fin (n + 1)) {A B : C}
    (hA : F.obj i = A) (hB : F.obj j = B) :
    hom F Y L i.castSucc j.castSucc ≫ eqToHom (congrArg₂ SimplicialCategory.sHom
      ((obj_cast F Y i).trans hA) ((obj_cast F Y j).trans hB)) =
    frontHom F i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) := by
  calc
    _ = (hom F Y L i.castSucc j.castSucc ≫ eqToHom
        (congrArg₂ SimplicialCategory.sHom (obj_cast F Y i) (obj_cast F Y j))) ≫
        eqToHom (congrArg₂ SimplicialCategory.sHom hA hB) := by
      simp only [Category.assoc, eqToHom_trans]
    _ = _ := by rw [hom_cast_cast]

lemma frontHom_fixed (i j : Fin (n + 1)) {X : C}
    (hI : F.obj i = X) (hJ : F.obj j = X)
    (hf : ∀ hij : i ≤ j, HEq (F.map (homOfLE hij)) (𝟙 X)) :
    frontHom F i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hI hJ) =
      toUnit _ ≫ eId SSet X := by
  apply SSet.hom_ext
  intro d
  apply ConcreteCategory.hom_ext
  intro P
  have hij := front_le i j (P.obj 0)
  have h : frontHom F i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom hI hJ) =
      toUnit _ ≫ eId SSet X := by
    rw [frontHom_const F i j hij, Category.assoc,
      unitHom_transport hI hJ (F.map (homOfLE hij)) (𝟙 X) (hf hij), eHomEquiv_id]
  exact ConcreteCategory.congr_hom (NatTrans.congr_app h d) P

variable (hL : ∀ (i j : Fin (n + 1)) (hij : i ≤ j),
  eComp SSet (vertex.{u} i.castSucc) (vertex j.castSucc) (vertex (Fin.last (n + 1))) ≫ L i =
    lift (toUnit _ ≫ eHomEquiv SSet (F.map (homOfLE hij))) (snd _ _ ≫ L j) ≫
      eComp SSet (F.obj i) (F.obj j) Y)

lemma diagram_eq_comparison {X : C} (hobj : ∀ i, F.obj i = X)
    (hmap : ∀ (i j : Fin (n + 1)) (hij : i ≤ j), HEq (F.map (homOfLE hij)) (𝟙 X))
    (σ : (SimplicialCategory.sHom X Y) _⦋n⦌)
    (hlast : ∀ i, L i ≫ eqToHom (congrArg₂ SimplicialCategory.sHom (hobj i) (rfl : Y = Y)) =
      pathLastMaximumMap i ≫ SSet.yonedaEquiv.symm σ) :
    diagram F Y L hL = coherentHomComparisonSimplex σ := by
  have ho (i : Fin (n + 2)) : obj F Y i = coherentHomComparisonObj X Y i := by
    induction i using Fin.lastCases
    · rw [obj_last, coherentHomComparisonObj_last]
    · rename_i i
      rw [obj_cast, coherentHomComparisonObj_cast]
      exact hobj i
  apply EnrichedFunctor.ext SSet (fun i => ho i.as.down)
  rintro ⟨⟨i⟩⟩ ⟨⟨j⟩⟩
  change hom F Y L i j ≫ eqToHom (congrArg₂ SimplicialCategory.sHom (ho i) (ho j)) =
    coherentHomComparisonHom σ i j
  induction i using Fin.lastCases <;> induction j using Fin.lastCases
  case last.last =>
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentHomComparisonObj_last X Y n) (coherentHomComparisonObj_last X Y n)))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [hom_last_last, coherentHomComparisonHom_last_last]
  case last.cast j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    intro P
    have h := Path.le (P.obj 0)
    change n + 1 ≤ j.val at h
    omega
  case cast.last i =>
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_last X Y n)))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [hom_cast_last_normalized F Y L i (hobj i), coherentHomComparisonHom_cast_last]
    exact hlast i
  case cast.cast i j =>
    apply (cancel_mono (eqToHom (congrArg₂ SimplicialCategory.sHom
      (coherentHomComparisonObj_cast X Y i) (coherentHomComparisonObj_cast X Y j)))).1
    simp only [Category.assoc, eqToHom_trans]
    rw [hom_cast_cast_normalized F Y L i j (hobj i) (hobj j),
      coherentHomComparisonHom_cast_cast]
    exact frontHom_fixed F i j (hobj i) (hobj j) (hmap i j)

end SerrePositivity.EInfinity.FrameHom.CoherentRightCone
