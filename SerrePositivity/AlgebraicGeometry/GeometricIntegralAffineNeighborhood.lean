module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-!
概要：幾何学的整な開写像を、指定点を残してアフィン近傍に制限する。
方針：始域のアフィン開の像の中に基底のアフィン近傍を取る。
規約：始域側の最後の制限は基底のアフィン近傍の逆像とする。
使われ方：相対 Noether 正規化先を有限加群を扱えるアフィン族に縮める。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits TopologicalSpace

/--
概要：幾何学的整な族の開部分が基底に全射なら、その開部分も幾何学的整な族になる。
方針：任意の体への底変換で、空でない開部分が整スキームに入ることを使う。
規約：始域の開部分は開埋め込みとして与える。
使われ方：幾何学的整な族を全射性を保つ開部分に制限する。
-/
theorem geometricallyIntegral_of_surjective_openImmersion_comp
    {X Y S : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ S)
    [IsOpenImmersion i] [GeometricallyIntegral f] [Surjective (i ≫ f)] :
    GeometricallyIntegral (i ≫ f) := by
  constructor
  intro K _ y Z fst snd h
  let j := pullback.map (i ≫ f) y f y i (𝟙 _) (𝟙 _) (by simp) (by simp)
  let : IsOpenImmersion j := inferInstance
  let : IsIntegral (pullback f y) :=
    GeometricallyIntegral.geometrically_isIntegral (f := f) y _ _ (.of_hasPullback _ _)
  obtain ⟨x, _⟩ := (pullback.snd (i ≫ f) y).surjective (⊥ : PrimeSpectrum K)
  let : Nonempty Z := ⟨h.isoPullback.inv x⟩
  exact isIntegral_of_isOpenImmersion (h.isoPullback.hom ≫ j)

/--
概要：幾何学的整な開写像で、指定点を含むアフィン開とその像に含まれる基底のアフィン近傍を選べる。
方針：アフィン開の逆像を取り、全射な開部分は幾何学的整であることを使う。
規約：基底がアフィンの場合を扱う。制限後の始域もアフィンになる。
使われ方：Stacks 057S の正規化先を幾何学的整なアフィン族に縮める。
-/
theorem exists_affine_geometricallyIntegral_neighborhood
    {X S : Scheme.{u}} [IsAffine S] (f : X ⟶ S)
    [GeometricallyIntegral f] (hf : IsOpenMap f) (x : X) :
    ∃ (V : X.Opens) (U : S.Opens), IsAffineOpen V ∧ x ∈ V ∧ IsAffineOpen U ∧ f x ∈ U ∧
      IsAffineOpen ((V.ι ≫ f) ⁻¹ᵁ U) ∧ GeometricallyIntegral ((V.ι ≫ f) ∣_ U) := by
  have hxTop : x ∈ (⊤ : X.Opens) := by simp
  obtain ⟨V₀, hV, hx, _⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hxTop
  let V : X.Opens := V₀
  let g : (V : Scheme) ⟶ S := V.ι ≫ f
  let W : S.Opens := ⟨Set.range g, (hf.comp V.ι.isOpenEmbedding.isOpenMap).isOpen_range⟩
  have hW : f x ∈ W := ⟨⟨x, hx⟩, rfl⟩
  obtain ⟨U₀, hU, hfx, hUW⟩ := Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens hW
  let U : S.Opens := U₀
  let : IsAffine (V : Scheme) := hV
  have hSurj : Surjective (g ∣_ U) := ⟨fun y => by
    obtain ⟨v, hv⟩ := hUW y.2
    refine ⟨⟨v, ?_⟩, ?_⟩
    · change g v ∈ U
      exact hv.symm ▸ y.2
    · exact Subtype.ext ((morphismRestrict_base_coe g U _).trans hv)⟩
  have hcomp : (V.ι ∣_ (f ⁻¹ᵁ U)) ≫ f ∣_ U = g ∣_ U :=
    (morphismRestrict_comp V.ι f U).symm
  let : Surjective ((V.ι ∣_ (f ⁻¹ᵁ U)) ≫ f ∣_ U) := hcomp.symm ▸ hSurj
  refine ⟨V, U, hV, hx, hU, hfx, hU.preimage g, ?_⟩
  rw [← hcomp]
  let : IsOpenImmersion (V.ι ∣_ (f ⁻¹ᵁ U)) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict V.ι (f ⁻¹ᵁ U)).flip
      (inferInstance : IsOpenImmersion V.ι)
  exact geometricallyIntegral_of_surjective_openImmersion_comp (V.ι ∣_ (f ⁻¹ᵁ U)) (f ∣_ U)

/--
概要：幾何学的整で相対次元が一定な滑らかな族への有限写像を、指定点を残してアフィンに縮める。
方針：正規化先のアフィン近傍を選び、有限写像を開埋め込みに沿って引き戻す。
規約：基底はアフィンとし、縮めた基底と正規化先から元への射は開埋め込みとする。
使われ方：Stacks 057S で得る滑らかな正規化先の幾何学的整な開部分から有限写像を回収する。
-/
theorem exists_affine_finite_refinement_of_geometricallyIntegral_smooth
    {X Y S : Scheme.{u}} [IsAffine S] (h : X ⟶ Y) [IsFinite h]
    (f : Y ⟶ S) {n : ℕ} [SmoothOfRelativeDimension n f] [GeometricallyIntegral f] (x : X) :
    ∃ (S' Y' X' : Scheme.{u}) (_ : IsAffine S') (_ : IsAffine Y') (_ : IsAffine X')
      (jS : S' ⟶ S) (jY : Y' ⟶ Y) (jX : X' ⟶ X) (f' : Y' ⟶ S') (h' : X' ⟶ Y') (x' : X'),
      IsOpenImmersion jS ∧ IsOpenImmersion jY ∧ f' ≫ jS = jY ≫ f ∧
      IsPullback jX h' h jY ∧ jX x' = x ∧
      IsFinite h' ∧ SmoothOfRelativeDimension n f' ∧ GeometricallyIntegral f' := by
  let : Smooth f := SmoothOfRelativeDimension.smooth (n := n) (f := f)
  obtain ⟨V, U, _, hxV, hU, hxU, hW, hInt⟩ :=
    exists_affine_geometricallyIntegral_neighborhood f f.isOpenMap (h x)
  let g := V.ι ≫ f
  let W := g ⁻¹ᵁ U
  let j := W.ι ≫ V.ι
  let : IsAffine (U : Scheme) := hU
  let : IsAffine (W : Scheme) := hW
  let y' : W := ⟨⟨h x, hxV⟩, hxU⟩
  obtain ⟨x', hx', _⟩ := Scheme.Pullback.exists_preimage_pullback x y' (f := h) (g := j) rfl
  have hg : SmoothOfRelativeDimension n g := by
    simpa only [zero_add] using
      (inferInstance : SmoothOfRelativeDimension (0 + n) (V.ι ≫ f))
  have hSmooth : SmoothOfRelativeDimension n (g ∣_ U) :=
    MorphismProperty.of_isPullback (isPullback_morphismRestrict g U).flip hg
  refine ⟨U, W, pullback h j, inferInstance, inferInstance, inferInstance, U.ι, j,
    pullback.fst h j, g ∣_ U, pullback.snd h j, x', inferInstance, inferInstance, ?_,
    .of_hasPullback _ _, hx', inferInstance, hSmooth, hInt⟩
  exact (morphismRestrict_ι g U).trans (Category.assoc ..).symm

end SerrePositivity.AlgebraicGeometry
