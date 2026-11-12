module

public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberComparisonPost
public import
SerrePositivity.Archive.InfinityCategories.FilteredExchange.RelativeExtensionFiberEndpointValue
public import
SerrePositivity.InfinityCategories.Project.FilteredExchange.RelativeFunctorCurryIsoPresentation
public import SerrePositivity.InfinityCategories.Project.QuasicategoryAuxiliaries.FunctorIsoWhiskerAlgebra

/-!
概要：元の二実延長の指定 fiber 比較は、全空間の後合成でも同じ指定値へ写る。
方針：可縮な延長空間の比較へ戻し、同じ終点評価の厳密自然性を使う。
規約：元の比較を保持。使われ方：元の指定輸送比較の後合成照合。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory MonoidalClosed SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.F2

/-- 元の指定終点比較を fiber 写像へ送ると、同じ実延長の像の指定比較になる。 -/
lemma relativeExtensionFiberEndpoint_witnessIso_post {A D C E F B : SSet.{u}}
    (p : E ⟶ B) (q : F ⟶ B) [LeftFibration p] [LeftFibration q]
    (f : E ⟶ F) (hf : f ≫ q = p) (b : A ⟶ B) (i : D ⟶ A)
    (hi : leftAnodyneExtensions i) (v : D ⟶ E) (hv : v ≫ p = i ≫ b)
    (j : C ⟶ A) (z : B _⦋0⦌) (hj : j ≫ b = SSet.const z)
    (W₀ W₁ : A ⟶ E) (h₀ : W₀ ≫ p = b) (h₁ : W₁ ≫ p = b)
    (hi₀ : i ≫ W₀ = v) (hi₁ : i ≫ W₁ = v) (g₀ g₁ : C ⟶ vertexFiber p z)
    (hj₀ : j ≫ W₀ = g₀ ≫ vertexFiberι p z) (hj₁ : j ≫ W₁ = g₁ ≫ vertexFiberι p z) :
    (relativeExtensionFiberEndpoint_witnessIso p b i hi v hv j z hj
      W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁).postcomp (vertexFiberMap p q f hf z) =
    relativeExtensionFiberEndpoint_witnessIso q b i hi (v ≫ f)
      (relativeExtensionPost_initial_base p q f hf b i v hv) j z hj
      (W₀ ≫ f) (W₁ ≫ f) (by rw [Category.assoc, hf, h₀])
      (by rw [Category.assoc, hf, h₁]) (by rw [← Category.assoc, hi₀])
      (by rw [← Category.assoc, hi₁]) (g₀ ≫ vertexFiberMap p q f hf z)
      (g₁ ≫ vertexFiberMap p q f hf z)
      (by rw [Category.assoc, vertexFiberMap_ι, ← Category.assoc, hj₀, Category.assoc])
      (by rw [Category.assoc, vertexFiberMap_ι, ← Category.assoc, hj₁, Category.assoc]) := by
  let x := relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W₀, h₀, hi₀⟩
  let y := relativeFunctorExtensionSpaceVertexEquiv p b i v hv ⟨W₁, h₁, hi₁⟩
  let e := (relativeFunctorExtensionSpace_isContractibleKan p b i hi v hv).vertexIso x y
  let P := relativeExtensionFiberEndpoint p b i v hv j z hj
  have he := relativeExtensionFiberEndpoint_witnessIso_heq_map p b i hi v hv j z hj
    W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁
  have hs := relativeExtensionFiberEndpoint_vertex p b i v hv j z hj W₀ h₀ hi₀ g₀ hj₀
  have ht := relativeExtensionFiberEndpoint_vertex p b i v hv j z hj W₁ h₁ hi₁ g₁ hj₁
  have hm := vertexIso_map_heq_of_heq
    (relativeExtensionFiberEndpoint_witnessIso p b i hi v hv j z hj
      W₀ W₁ h₀ h₁ hi₀ hi₁ g₀ g₁ hj₀ hj₁) (VertexIso.map e P) hs.symm ht.symm he
    ((ihom C).map (vertexFiberMap p q f hf z))
  have hc := relativeExtensionFiberComparison_post p q f hf b i hi v hv j z hj x y
  dsimp only [x, y] at hc
  rw [relativeExtensionPost_vertex p q f hf b i v hv W₀ h₀ hi₀,
    relativeExtensionPost_vertex p q f hf b i v hv W₁ h₁ hi₁] at hc
  have he' := relativeExtensionFiberEndpoint_witnessIso_heq_map q b i hi (v ≫ f)
    (relativeExtensionPost_initial_base p q f hf b i v hv) j z hj
    (W₀ ≫ f) (W₁ ≫ f) (by rw [Category.assoc, hf, h₀])
    (by rw [Category.assoc, hf, h₁]) (by rw [← Category.assoc, hi₀])
    (by rw [← Category.assoc, hi₁]) (g₀ ≫ vertexFiberMap p q f hf z)
    (g₁ ≫ vertexFiberMap p q f hf z)
    (by rw [Category.assoc, vertexFiberMap_ι, ← Category.assoc, hj₀, Category.assoc])
    (by rw [Category.assoc, vertexFiberMap_ι, ← Category.assoc, hj₁, Category.assoc])
  apply eq_of_heq
  apply HEq.trans _ (hc.trans he'.symm)
  simpa only [functorIso_postcomp_eq_mapIso, VertexIso.map, hoFunctor_map,
    Functor.toCatHom_toFunctor] using hm

end SerrePositivity.InfinityCategories.F2
