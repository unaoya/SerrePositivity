module

public import SerrePositivity.BhattScholze.Prism.PCompletedDeltaRegularity

/-! # p進完備なδ完全化の具体的な延長射と関手性

著者公開版Lemma 3.9のp進完備化段階。
既存の存在・一意性から公開環射を取り出し、恒等射・合成との両立を証明する。
(p,d)導来完備化やprismの完全化全体とは区別する。
-/

@[expose] public noncomputable section
universe u v w
namespace SerrePositivity.BhattScholze
variable {p : ℕ} [Fact p.Prime]
variable {A : Type u} {B : Type v} {C : Type w} [CommRing A] [CommRing B] [CommRing C]

/-- 完全かつp進完備なδ終域への具体的な一意延長射。 -/
def pCompletedDeltaLift (D : DeltaStructure p A) (E : DeltaStructure p B)
    (hE : E.IsPerfect) [IsAdicComplete (Ideal.span {(p : B)}) B]
    (f : A →+* B) (hf : D.IsDeltaHom E f) : PCompletedDeltaPerfection D →+* B :=
  (existsUnique_pCompletedDeltaPerfectionHom D E hE f hf).choose

/-- 選んだ延長射はδ射。 -/
theorem pCompletedDeltaLift_isDeltaHom (D : DeltaStructure p A) (E : DeltaStructure p B)
    (hE : E.IsPerfect) [IsAdicComplete (Ideal.span {(p : B)}) B]
    (f : A →+* B) (hf : D.IsDeltaHom E f) :
    (pCompletedDeltaPerfectionStructure D).IsDeltaHom E (pCompletedDeltaLift D E hE f hf) :=
  (existsUnique_pCompletedDeltaPerfectionHom D E hE f hf).choose_spec.1.1

/-- 延長射は元の基底射に一致する。 -/
@[simp] theorem pCompletedDeltaLift_comp_map (D : DeltaStructure p A) (E : DeltaStructure p B)
    (hE : E.IsPerfect) [IsAdicComplete (Ideal.span {(p : B)}) B]
    (f : A →+* B) (hf : D.IsDeltaHom E f) :
    (pCompletedDeltaLift D E hE f hf).comp (pCompletedDeltaPerfectionMap D) = f :=
  (existsUnique_pCompletedDeltaPerfectionHom D E hE f hf).choose_spec.1.2

/-- 基底射に一致する任意のδ射は具体的な延長射と等しい。 -/
theorem pCompletedDeltaLift_unique (D : DeltaStructure p A) (E : DeltaStructure p B)
    (hE : E.IsPerfect) [IsAdicComplete (Ideal.span {(p : B)}) B]
    (f : A →+* B) (hf : D.IsDeltaHom E f) (g : PCompletedDeltaPerfection D →+* B)
    (hg : (pCompletedDeltaPerfectionStructure D).IsDeltaHom E g)
    (hgf : g.comp (pCompletedDeltaPerfectionMap D) = f) :
    g = pCompletedDeltaLift D E hE f hf :=
  (existsUnique_pCompletedDeltaPerfectionHom D E hE f hf).choose_spec.2 g ⟨hg, hgf⟩

/-- p進完備なδ完全化からのδ射は基底上の値で決まる。 -/
theorem pCompletedDeltaHom_ext (D : DeltaStructure p A) (E : DeltaStructure p B)
    (hE : E.IsPerfect) [IsAdicComplete (Ideal.span {(p : B)}) B]
    (f g : PCompletedDeltaPerfection D →+* B)
    (hf : (pCompletedDeltaPerfectionStructure D).IsDeltaHom E f)
    (hg : (pCompletedDeltaPerfectionStructure D).IsDeltaHom E g)
    (hfg : f.comp (pCompletedDeltaPerfectionMap D) =
      g.comp (pCompletedDeltaPerfectionMap D)) : f = g := by
  let j := pCompletedDeltaPerfectionMap D
  have hgj := hg.comp (pCompletedDeltaPerfectionMap_isDeltaHom D)
  exact (pCompletedDeltaLift_unique D E hE (g.comp j) hgj f hf hfg).trans
    (pCompletedDeltaLift_unique D E hE (g.comp j) hgj g hg rfl).symm

/-- δ射が誘導するp進完備なδ完全化の間の具体的な射。 -/
def pCompletedDeltaMap (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f) :
    PCompletedDeltaPerfection D →+* PCompletedDeltaPerfection E := by
  let := pCompletedDeltaPerfection_isAdicComplete E
  exact pCompletedDeltaLift D (pCompletedDeltaPerfectionStructure E)
    (pCompletedDeltaPerfection_isPerfect E) ((pCompletedDeltaPerfectionMap E).comp f)
    ((pCompletedDeltaPerfectionMap_isDeltaHom E).comp hf)

/-- 誘導射はδ射。 -/
theorem pCompletedDeltaMap_isDeltaHom (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f) :
    (pCompletedDeltaPerfectionStructure D).IsDeltaHom (pCompletedDeltaPerfectionStructure E)
      (pCompletedDeltaMap D E f hf) := by
  let := pCompletedDeltaPerfection_isAdicComplete E
  exact pCompletedDeltaLift_isDeltaHom D (pCompletedDeltaPerfectionStructure E)
    (pCompletedDeltaPerfection_isPerfect E) _
    ((pCompletedDeltaPerfectionMap_isDeltaHom E).comp hf)

/-- 誘導射は標準射と可換。 -/
@[simp] theorem pCompletedDeltaMap_comp_map (D : DeltaStructure p A) (E : DeltaStructure p B)
    (f : A →+* B) (hf : D.IsDeltaHom E f) :
    (pCompletedDeltaMap D E f hf).comp (pCompletedDeltaPerfectionMap D) =
      (pCompletedDeltaPerfectionMap E).comp f := by
  let := pCompletedDeltaPerfection_isAdicComplete E
  exact pCompletedDeltaLift_comp_map D (pCompletedDeltaPerfectionStructure E)
    (pCompletedDeltaPerfection_isPerfect E) _
    ((pCompletedDeltaPerfectionMap_isDeltaHom E).comp hf)

/-- 恒等δ射の誘導射は恒等射。 -/
@[simp] theorem pCompletedDeltaMap_id (D : DeltaStructure p A) :
    pCompletedDeltaMap D D (RingHom.id A) D.isDeltaHom_id =
      RingHom.id (PCompletedDeltaPerfection D) := by
  let := pCompletedDeltaPerfection_isAdicComplete D
  apply pCompletedDeltaHom_ext D _ (pCompletedDeltaPerfection_isPerfect D)
    _ _ (pCompletedDeltaMap_isDeltaHom D D _ _) (pCompletedDeltaPerfectionStructure D).isDeltaHom_id
  simp only [pCompletedDeltaMap_comp_map, RingHom.comp_id, RingHom.id_comp]

/-- 合成δ射の誘導射は誘導射の合成。 -/
theorem pCompletedDeltaMap_comp (D : DeltaStructure p A) (E : DeltaStructure p B)
    (F : DeltaStructure p C) (f : A →+* B) (hf : D.IsDeltaHom E f)
    (g : B →+* C) (hg : E.IsDeltaHom F g) :
    pCompletedDeltaMap D F (g.comp f) (hg.comp hf) =
      (pCompletedDeltaMap E F g hg).comp (pCompletedDeltaMap D E f hf) := by
  let := pCompletedDeltaPerfection_isAdicComplete F
  apply pCompletedDeltaHom_ext D _ (pCompletedDeltaPerfection_isPerfect F)
    _ _ (pCompletedDeltaMap_isDeltaHom D F _ _)
    ((pCompletedDeltaMap_isDeltaHom E F g hg).comp (pCompletedDeltaMap_isDeltaHom D E f hf))
  rw [pCompletedDeltaMap_comp_map]
  symm
  calc
    ((pCompletedDeltaMap E F g hg).comp (pCompletedDeltaMap D E f hf)).comp
        (pCompletedDeltaPerfectionMap D) =
        (pCompletedDeltaMap E F g hg).comp
          ((pCompletedDeltaMap D E f hf).comp (pCompletedDeltaPerfectionMap D)) :=
      RingHom.comp_assoc _ _ _
    _ = (pCompletedDeltaMap E F g hg).comp ((pCompletedDeltaPerfectionMap E).comp f) := by
      rw [pCompletedDeltaMap_comp_map]
    _ = ((pCompletedDeltaMap E F g hg).comp (pCompletedDeltaPerfectionMap E)).comp f :=
      (RingHom.comp_assoc _ _ _).symm
    _ = ((pCompletedDeltaPerfectionMap F).comp g).comp f := by
      rw [pCompletedDeltaMap_comp_map]
    _ = (pCompletedDeltaPerfectionMap F).comp (g.comp f) := RingHom.comp_assoc _ _ _

end SerrePositivity.BhattScholze
