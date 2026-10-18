module

public import SerrePositivity.KST.DerivedBlowup.ExteriorDGFunctor

/-!
概要：KST §3.1 の基底変換の合成を整数次数と dg 関手で保持する。
方針：chain 複体での関手性を零延長し、豊穣関手の外延性を用いる。
規約：微分適合性の証明項の選び方には依存しない。
使われ方：チャート遷移の cocycle と逆写像。
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false

universe u

namespace SerrePositivity.KST.DerivedBlowup

open CategoryTheory

variable {R M N P : Type u} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  [AddCommGroup P] [Module R P]

/-- 概要：Koszul cochain map は生成元の恒等写像を保つ。
方針：chain map の恒等則を零延長する。
規約：KST §3.1。使われ方：チャートの恒等遷移。 -/
theorem exteriorKoszulCochainMap_id (d : M →ₗ[R] R) (h : d.comp LinearMap.id = d) :
    exteriorKoszulCochainMap LinearMap.id d d h = 𝟙 _ := by
  dsimp only [exteriorKoszulCochainMap]
  rw [exteriorKoszulChainMap_id, HomologicalComplex.extendMap_id]
  rfl

/-- 概要：Koszul cochain map は生成元変換の合成を保つ。
方針：chain map の合成則と extendMap_comp を使う。
規約：KST §3.1。使われ方：三重重なりの cocycle。 -/
theorem exteriorKoszulCochainMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (dM : M →ₗ[R] R) (dN : N →ₗ[R] R) (dP : P →ₗ[R] R)
    (hf : dN.comp f = dM) (hg : dP.comp g = dN) (hgf : dP.comp (g.comp f) = dM) :
    exteriorKoszulCochainMap f dM dN hf ≫ exteriorKoszulCochainMap g dN dP hg =
      exteriorKoszulCochainMap (g.comp f) dM dP hgf := by
  dsimp only [exteriorKoszulCochainMap]
  rw [← HomologicalComplex.extendMap_comp, exteriorKoszulChainMap_comp f g dM dN dP hf hg hgf]

/-- 概要：Koszul dg 関手は生成元の恒等写像を保つ。
方針：対象写像は一対象型の一意性、Hom は cochain map の恒等則。
規約：KST §3.1。使われ方：dg チャート図式の恒等則。 -/
theorem exteriorKoszulDGFunctor_id (d : M →ₗ[R] R) (h : d.comp LinearMap.id = d) :
    exteriorKoszulDGFunctor LinearMap.id d d h =
      EnrichedFunctor.id (DifferentialGraded.Complex R) (ExteriorKoszulObject d) := by
  apply EnrichedFunctor.ext (DifferentialGraded.Complex R) (fun x => by cases x; rfl)
  intro x y
  simp only [exteriorKoszulDGFunctor, EnrichedFunctor.id, eqToHom_refl, Category.comp_id]
  exact exteriorKoszulCochainMap_id d h

/-- 概要：Koszul dg 関手は生成元変換の合成を保つ。
方針：一対象型の対象写像と cochain map の合成則を比較する。
規約：KST §3.1。使われ方：dg チャート遷移の cocycle。 -/
theorem exteriorKoszulDGFunctor_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P)
    (dM : M →ₗ[R] R) (dN : N →ₗ[R] R) (dP : P →ₗ[R] R)
    (hf : dN.comp f = dM) (hg : dP.comp g = dN) (hgf : dP.comp (g.comp f) = dM) :
    EnrichedFunctor.comp (DifferentialGraded.Complex R)
      (exteriorKoszulDGFunctor f dM dN hf) (exteriorKoszulDGFunctor g dN dP hg) =
      exteriorKoszulDGFunctor (g.comp f) dM dP hgf := by
  refine EnrichedFunctor.ext (DifferentialGraded.Complex R)
    (F := EnrichedFunctor.comp (DifferentialGraded.Complex R)
      (exteriorKoszulDGFunctor f dM dN hf) (exteriorKoszulDGFunctor g dN dP hg))
    (G := exteriorKoszulDGFunctor (g.comp f) dM dP hgf) (fun _ => rfl) ?_
  intro x y
  simp only [EnrichedFunctor.comp, exteriorKoszulDGFunctor, eqToHom_refl, Category.comp_id]
  exact exteriorKoszulCochainMap_comp f g dM dN dP hf hg hgf

end SerrePositivity.KST.DerivedBlowup
