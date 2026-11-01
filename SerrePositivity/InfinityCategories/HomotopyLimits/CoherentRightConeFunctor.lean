module

public import SerrePositivity.InfinityCategories.HomotopyLimits.CoherentRightConeHom

/-!
# 元の前面と全最後 Hom の coherent 錐への組立

概要：最後 Hom の元の合成式から全豊穣関手を構成する。
方針：全頂点の場合を分け、通常の関手則・元の path 合成・豊穣単位則を使う。
規約：合成式を検証した具体的な Hom のみを代入する。
使われ方：native roof の混合 coherent 図式の全単体。
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

lemma id_iff_normalized {A A' : C} (h : A = A') {K : SSet.{u}}
    (s : 𝟙_ SSet.{u} ⟶ K) (f : K ⟶ SimplicialCategory.sHom A A) :
    s ≫ f = eId SSet A ↔
      s ≫ (f ≫ eqToHom (congrArg₂ SimplicialCategory.sHom h h)) = eId SSet A' := by
  cases h
  simp only [eqToHom_refl, Category.comp_id]

lemma hom_map_id (i : Fin (n + 2)) :
    eId SSet (vertex.{u} i) ≫ hom F Y L i i = eId SSet (obj F Y i) := by
  induction i using Fin.lastCases with
  | last =>
    apply (id_iff_normalized (obj_last F Y) _ _).2
    rw [hom_last_last]
    simp only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp]
  | cast i =>
    apply (id_iff_normalized (obj_cast F Y i) _ _).2
    rw [hom_cast_cast, frontHom_const F i i le_rfl]
    simp only [← Category.assoc, comp_toUnit, toUnit_unit, Category.id_comp,
      show homOfLE (show i ≤ i from le_rfl) = 𝟙 i from rfl, F.map_id, eHomEquiv_id]

variable (hL : ∀ (i j : Fin (n + 1)) (hij : i ≤ j),
  eComp SSet (vertex.{u} i.castSucc) (vertex j.castSucc) (vertex (Fin.last (n + 1))) ≫ L i =
    lift (toUnit _ ≫ eHomEquiv SSet (F.map (homOfLE hij))) (snd _ _ ≫ L j) ≫
      eComp SSet (F.obj i) (F.obj j) Y)

include hL in
lemma hom_map_comp (i j k : Fin (n + 2)) :
    eComp SSet (vertex.{u} i) (vertex j) (vertex k) ≫ hom F Y L i k =
      (hom F Y L i j ⊗ₘ hom F Y L j k) ≫
        eComp SSet (obj F Y i) (obj F Y j) (obj F Y k) := by
  let hY := obj_last F Y
  let hF := obj_cast F Y
  induction i using Fin.lastCases <;> induction j using Fin.lastCases <;>
    induction k using Fin.lastCases
  case last.last.last =>
    apply (simplicialHom_map_comp_iff_normalized hY hY hY _ _ _ _).2
    simp only [hom_last_last]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    change (eId SSet Y).app d PUnit.unit = (eComp SSet Y Y Y).app d
      ((eId SSet Y).app d PUnit.unit, (eId SSet Y).app d PUnit.unit)
    exact (simplicialHom_id_comp_app Y Y d _).symm
  case last.last.cast k =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    have h := Path.le (Q.obj 0)
    change n + 1 ≤ k.val at h
    omega
  case last.cast.last j =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    have h := Path.le (P.obj 0)
    change n + 1 ≤ j.val at h
    omega
  case last.cast.cast j k =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    have h := Path.le (P.obj 0)
    change n + 1 ≤ j.val at h
    omega
  case cast.last.cast i k =>
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    have h := Path.le (Q.obj 0)
    change n + 1 ≤ k.val at h
    omega
  case cast.last.last i =>
    apply (simplicialHom_map_comp_iff_normalized (hF i) hY hY _ _ _ _).2
    simp only [hom_cast_last, hom_last_last]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    change (L i).app d ((eComp SSet (vertex i.castSucc)
      (vertex (Fin.last (n + 1))) (vertex (Fin.last (n + 1)))).app d (P, Q)) =
      (eComp SSet (F.obj i) Y Y).app d ((L i).app d P, (eId SSet Y).app d PUnit.unit)
    rw [thickeningHom_comp_end_right]
    exact (simplicialHom_comp_id_app (F.obj i) Y d _).symm
  case cast.cast.last i j =>
    apply (simplicialHom_map_comp_iff_normalized (hF i) (hF j) hY _ _ _ _).2
    simp only [hom_cast_last, hom_cast_cast]
    apply SSet.hom_ext
    intro d
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    have hij := front_le i j (P.obj 0)
    have he := NatTrans.congr_app (hL i j hij) d
    have h := ConcreteCategory.congr_hom he
      (show ((SimplicialCategory.sHom (vertex i.castSucc) (vertex j.castSucc)) ⊗
        SimplicialCategory.sHom (vertex j.castSucc) (vertex (Fin.last (n + 1)))).obj d from
          (P, Q))
    change (L i).app d ((eComp SSet (vertex i.castSucc) (vertex j.castSucc)
      (vertex (Fin.last (n + 1)))).app d (P, Q)) = (eComp SSet (F.obj i) (F.obj j) Y).app d
        ((eHomEquiv SSet (F.map (homOfLE hij))).app d PUnit.unit, (L j).app d Q) at h
    rw [unitHom_app_constant] at h
    exact h
  case cast.cast.cast i j k =>
    apply (simplicialHom_map_comp_iff_normalized (hF i) (hF j) (hF k) _ _ _ _).2
    simp only [hom_cast_cast]
    apply SSet.hom_ext
    rintro ⟨⟨d⟩⟩
    apply ConcreteCategory.hom_ext
    rintro ⟨P, Q⟩
    change PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (F.map (homOfLE _))) d =
      (eComp SSet (F.obj i) (F.obj j) (F.obj k)).app _
        (PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (F.map (homOfLE _))) d,
          PinchedHom.constant (SimplicialCategory.homEquiv' _ _ (F.map (homOfLE _))) d)
    rw [simplicialHom_constant_comp, ← F.map_comp]
    rfl

def diagram : EnrichedFunctor SSet.{u}
    (SimplicialThickening (ULift.{u} (Fin (n + 2)))) C where
  obj i := obj F Y i.as.down
  map i j := hom F Y L i.as.down j.as.down
  map_id i := hom_map_id F Y L i.as.down
  map_comp i j k := hom_map_comp F Y L hL i.as.down j.as.down k.as.down

end SerrePositivity.EInfinity.FrameHom.CoherentRightCone
