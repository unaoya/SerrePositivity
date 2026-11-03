module

public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.FiberTransportFamilyPrismComparison
public import SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberWitnessPrecomp

/-!
概要：元の二つの実輸送 prism の係数制限を、同じ指定 endpointIso の前合成で読む。
方針：元の fiber 比較の終点前合成と、同じ実 prism への制限を合成する。
規約：元の全輸送と実両端を保持。使われ方：同じ一点比較の全係数への移送。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2
variable {E B K L C : SSet.{u}} (p : E ⟶ B) [LeftFibration p] {a b : B _⦋0⦌}
  (f : K ⟶ vertexFiber p a) (γ : (Δ[1] : SSet.{u}) ⊗ L ⟶ B)
  (h₁ : prismEndpoint 1 L ≫ γ = SSet.const b)
  (T U : FiberTransportFamily (b := b) p f γ) (s : C ⟶ K ⊗ L)
local notation "β" => (Δ[1] ◁ snd K L) ≫ γ
local notation "v" => fst K L ≫ f ≫ vertexFiberι p a
local notation "h" => Δ[1] ◁ s

/-- 元の二つの実輸送 prism を同じ係数射で制限した指定 fiber 比較。 -/
def fiberTransportRestrictedPrismComparison : FunctorIso (s ≫ T.endpoint) (s ≫ U.endpoint) :=
  relativeExtensionFiberEndpoint_witnessIso p (h ≫ β) (prismEndpoint 0 C)
    (prismEndpoint_zero_leftAnodyne C) (s ≫ v)
    (by
      rw [← T.start]
      simp only [Category.assoc]
      rw [T.over_base, ← Category.assoc s (prismEndpoint 0 (K ⊗ L)),
        ← prismEndpoint_naturality, Category.assoc])
    (prismEndpoint 1 C) b (by
      rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
        fiberTransportFamily_base_endpoint 1 γ b h₁, SSet.comp_const])
    (h ≫ T.prism) (h ≫ U.prism)
    (by rw [Category.assoc, T.over_base]) (by rw [Category.assoc, U.over_base])
    (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, T.start])
    (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc, U.start])
    (s ≫ T.endpoint) (s ≫ U.endpoint)
    (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      T.finish, Category.assoc])
    (by rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      U.finish, Category.assoc])

/-- 同じ実係数制限の指定比較は、元の endpointIso の同じ前合成に厳密に一致する。 -/
lemma fiberTransportRestrictedPrismComparison_eq_endpointIso :
    fiberTransportRestrictedPrismComparison p f γ h₁ T U s =
      (T.endpointIso p f γ h₁ U).precomp s := by
  have hv : v ≫ p = prismEndpoint 0 (K ⊗ L) ≫ β := by
    rw [← T.start, Category.assoc, T.over_base]
  have hp := relativeExtensionFiberEndpoint_witnessIso_precomp p β
    (prismEndpoint 0 (K ⊗ L)) (prismEndpoint_zero_leftAnodyne (K ⊗ L)) v hv
    (prismEndpoint 1 (K ⊗ L)) b (fiberTransportFamily_base_endpoint 1 γ b h₁)
    T.prism U.prism T.over_base U.over_base T.start U.start T.endpoint U.endpoint
    T.finish U.finish s
  have hr := relativeExtensionFiberEndpoint_witnessIso_restriction p β
    (prismEndpoint 0 (K ⊗ L)) (prismEndpoint_zero_leftAnodyne (K ⊗ L)) v hv h s
    (prismEndpoint 0 C) (prismEndpoint_zero_leftAnodyne C)
    (prismEndpoint_naturality 0 s) (s ≫ prismEndpoint 1 (K ⊗ L)) (prismEndpoint 1 C)
    (prismEndpoint_naturality 1 s) b
    (by rw [Category.assoc, fiberTransportFamily_base_endpoint 1 γ b h₁, SSet.comp_const])
    T.prism U.prism T.over_base U.over_base T.start U.start
    (s ≫ T.endpoint) (s ≫ U.endpoint)
    (by rw [Category.assoc, T.finish, Category.assoc])
    (by rw [Category.assoc, U.finish, Category.assoc])
  calc
    _ = (fiberTransportFamilyPrismComparison p f γ h₁ T U).precomp s := (hp.trans hr).symm
    _ = _ := congrArg (fun e => e.precomp s)
      (fiberTransportFamilyPrismComparison_eq_endpointIso p f γ h₁ T U)

end SerrePositivity.InfinityCategories.F2
