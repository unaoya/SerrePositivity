module

public import SerrePositivity.AlgebraicGeometry.GeometricIntegralDescent

/-!
概要：有限標識上の幾何学的整な開部分が降下するとき、降下した開部分も幾何学的に整。
方針：基底と開部分の制限を引き戻しとして比較し、全射に沿って幾何学的整性を降ろす。
規約：基底は標識が全射となる開部分に縮めておく。
使われ方：相対 Noether 正規化の滑らかな始域を幾何学的整なファイバーの族に縮める。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits

/--
概要：標識上の幾何学的整な開部分が、縮めた基底上の開部分の逆像なら、元の開部分も幾何学的に整。
方針：標識の制限と開部分の逆像を同じ引き戻しにし、標識の全射性を使う。
規約：幾何学的整性の結論は、指定した基底の開部分への射について述べる。
使われ方：Stacks 057I と 057J の滑らかな場合。
-/
theorem geometricallyIntegral_marker_open_of_surjective_restrict
    {X Y S T : Scheme.{u}} {i : Y ⟶ X} {f' : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (hPb : IsPullback i f' f g) (U : S.Opens) (V : X.Opens) (W : Y.Opens)
    (hVU : V ≤ f ⁻¹ᵁ U) [Surjective (g ∣_ U)]
    (hEq : i ⁻¹ᵁ V = W ⊓ (f' ≫ g) ⁻¹ᵁ U) [GeometricallyIntegral (W.ι ≫ f')] :
    GeometricallyIntegral (X.homOfLE hVU ≫ f ∣_ U) := by
  let E := i ⁻¹ᵁ V
  let TU := g ⁻¹ᵁ U
  let WU := (W.ι ≫ f') ⁻¹ᵁ TU
  let j := WU.ι ≫ W.ι
  have hRange : Set.range j = Set.range E.ι := by
    rw [show j = WU.ι ≫ W.ι from rfl]
    change Set.range (⇑W.ι ∘ ⇑WU.ι) = _
    rw [Set.range_comp, Scheme.Opens.range_ι, Scheme.Opens.range_ι]
    change W.ι '' (W.ι ⁻¹' ((f' ≫ g) ⁻¹' (U : Set S))) = (E : Set Y)
    rw [Set.image_preimage_eq_inter_range, Scheme.Opens.range_ι, Set.inter_comm]
    exact congrArg (fun O : Y.Opens => (O : Set Y)) hEq.symm
  let e : (WU : Scheme) ≅ (E : Scheme) := IsOpenImmersion.isoOfRangeEq j E.ι hRange
  let hW : (WU : Scheme) ⟶ (TU : Scheme) := (W.ι ≫ f') ∣_ TU
  let hE : (E : Scheme) ⟶ (TU : Scheme) := e.inv ≫ hW
  let hV : (V : Scheme) ⟶ (U : Scheme) := X.homOfLE hVU ≫ f ∣_ U
  have he : hE ≫ TU.ι = E.ι ≫ f' := by
    calc
      hE ≫ TU.ι = e.inv ≫ (hW ≫ TU.ι) := Category.assoc ..
      _ = e.inv ≫ (WU.ι ≫ W.ι ≫ f') := by
        rw [show hW ≫ TU.ι = WU.ι ≫ W.ι ≫ f' from morphismRestrict_ι (W.ι ≫ f') TU]
      _ = E.ι ≫ f' := by
        rw [← Category.assoc]
        exact congrArg (fun k : (E : Scheme) ⟶ Y => k ≫ f')
          (IsOpenImmersion.isoOfRangeEq_inv_fac j E.ι hRange)
  have hv : hV ≫ U.ι = V.ι ≫ f := by
    simp [hV, Category.assoc]
  have hOuter := (isPullback_morphismRestrict i V).paste_vert hPb
  change IsPullback (i ∣_ V) (E.ι ≫ f') (V.ι ≫ f) g at hOuter
  have hComm : hE ≫ (g ∣_ U) = (i ∣_ V) ≫ hV := by
    apply (cancel_mono U.ι).mp
    calc
      (hE ≫ (g ∣_ U)) ≫ U.ι = (hE ≫ TU.ι) ≫ g := by simp [Category.assoc, TU]
      _ = (E.ι ≫ f') ≫ g := by rw [he]
      _ = (i ∣_ V) ≫ (V.ι ≫ f) := hOuter.w.symm
      _ = ((i ∣_ V) ≫ hV) ≫ U.ι := by rw [Category.assoc, hv]
  have hOuter' : IsPullback (hE ≫ TU.ι) (i ∣_ V) g (hV ≫ U.ι) := by
    rw [he, hv]
    exact hOuter.flip
  have hCart : IsPullback (i ∣_ V) hE hV (g ∣_ U) :=
    (IsPullback.of_right hOuter' hComm (isPullback_morphismRestrict g U).flip).flip
  have hIso : IsPullback e.inv hE hW (𝟙 _) :=
    IsPullback.of_horiz_isIso ⟨by simp [hE]⟩
  let : GeometricallyIntegral hE :=
    MorphismProperty.of_isPullback hIso (inferInstance : GeometricallyIntegral hW)
  exact geometricallyIntegral_of_surjective_baseChange hCart

end SerrePositivity.AlgebraicGeometry
