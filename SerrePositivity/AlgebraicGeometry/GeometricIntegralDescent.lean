module

public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-!
概要：忠実平坦な被覆に沿って整性と幾何学的整性を降下する。
方針：位相的既約性は全射性で降ろし、被約性は忠実平坦な茎写像の単射性で降ろす。
規約：幾何学的整性は、すべての体への底変換で判定する。
使われ方：有限標識上の切断を通る開成分から、元の滑らかな族の幾何学的整性を得る。
-/

@[expose] public noncomputable section

namespace SerrePositivity.AlgebraicGeometry

open _root_.AlgebraicGeometry CategoryTheory Limits

/--
概要：整スキームからの平坦全射の標的は整。
方針：既約性を連続全射で降ろし、被約な茎への単射で各茎の被約性を示す。
規約：茎写像は平坦かつ局所なので忠実平坦。
使われ方：幾何学的整性の降下。
-/
theorem isIntegral_of_flat_surjective
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Flat f] [Surjective f] [IsIntegral X] :
    IsIntegral Y := by
  refine (isIntegral_iff_irreducibleSpace_and_isReduced Y).mpr
    ⟨f.surjective.irreducibleSpace f.continuous, ?_⟩
  have h (y : Y) : _root_.IsReduced (Y.presheaf.stalk y) := by
    obtain ⟨x, rfl⟩ := f.surjective y
    let A := Y.presheaf.stalk (f x)
    let B := X.presheaf.stalk x
    let φ : A →+* B := (f.stalkMap x).hom
    let : Algebra A B := φ.toAlgebra
    let : Module.Flat A B := RingHom.flat_algebraMap_iff.mp (Flat.stalkMap f x)
    let : IsLocalHom (algebraMap A B) :=
      inferInstanceAs (IsLocalHom (f.stalkMap x).hom)
    let : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    exact isReduced_of_injective φ (FaithfulSMul.algebraMap_injective A B)
  exact isReduced_of_isReduced_stalk Y

/--
概要：全射に沿う底変換が幾何学的に整なら、もとの射も幾何学的に整。
方針：任意の体への底変換に対して全射のファイバーに点を選び、その剰余体まで拡大して整性を降ろす。
規約：比較に使う平坦全射は、体の拡大による底変換で作る。
使われ方：有限標識で切断を通る成分の幾何学的整性を元の基底へ戻す。
-/
theorem geometricallyIntegral_of_surjective_baseChange
    {X Y S T : Scheme.{u}} {i : Y ⟶ X} {f' : Y ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
    (hPb : IsPullback i f' f g) [Surjective g] [GeometricallyIntegral f'] :
    GeometricallyIntegral f := by
  constructor
  intro K _ q W a b hK
  let Z := pullback g q
  obtain ⟨z, _⟩ := (pullback.snd g q).surjective (⊥ : PrimeSpectrum K)
  let L := Z.residueField z
  let ρ : Spec L ⟶ Z := Z.fromSpecResidueField z
  let y : Spec L ⟶ T := ρ ≫ pullback.fst g q
  let ℓ : Spec L ⟶ Spec (.of K) := ρ ≫ pullback.snd g q
  have hℓ : y ≫ g = ℓ ≫ q := by
    simpa only [y, ℓ, Category.assoc] using congrArg (fun k : Z ⟶ S => ρ ≫ k)
      (pullback.condition (f := g) (g := q))
  let : Flat ℓ := inferInstance
  let : Surjective ℓ := ⟨fun t => ⟨default, Subsingleton.elim _ _⟩⟩
  let P := pullback f' y
  let fst : P ⟶ Y := pullback.fst f' y
  let snd : P ⟶ Spec L := pullback.snd f' y
  have hOuter := (IsPullback.of_hasPullback f' y).paste_horiz hPb
  change IsPullback (fst ≫ i) snd f (y ≫ g) at hOuter
  rw [hℓ] at hOuter
  have hComm : (fst ≫ i) ≫ f = (snd ≫ ℓ) ≫ q := hOuter.w.trans (Category.assoc ..).symm
  let α : P ⟶ W := hK.lift (fst ≫ i) (snd ≫ ℓ) hComm
  have hαa : α ≫ a = fst ≫ i := hK.lift_fst _ _ _
  have hαb : α ≫ b = snd ≫ ℓ := hK.lift_snd _ _ _
  have hα : IsPullback α snd b ℓ :=
    IsPullback.of_right (hαa.symm ▸ hOuter) hαb hK
  let : Flat α := MorphismProperty.of_isPullback hα.flip (inferInstance : Flat ℓ)
  let : Surjective α := MorphismProperty.of_isPullback hα.flip (inferInstance : Surjective ℓ)
  have hG : geometrically IsIntegral f' := GeometricallyIntegral.geometrically_isIntegral
  let : IsIntegral P := hG y fst snd (IsPullback.of_hasPullback f' y)
  exact isIntegral_of_flat_surjective α

end SerrePositivity.AlgebraicGeometry
