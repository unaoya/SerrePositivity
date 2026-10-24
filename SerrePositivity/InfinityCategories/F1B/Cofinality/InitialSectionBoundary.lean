module

public import SerrePositivity.InfinityCategories.F1B.Cofinality.InitialSectionTransport
public import SerrePositivity.InfinityCategories.F1B.Fibrations.SectionPrism
public import SerrePositivity.InfinityCategories.F1B.Fibrations.CocartesianHomotopyGluing

/-!
概要：部分パラメータ上の section と始対象での評価を同時に固定して延長する。
方針：部分パラメータ上の収縮による輸送と頂点部分上の定値輸送を積の和で貼る。
規約：指定部分は任意の部分複体であり、境界のみに制限しない。
使われ方：始対象での cocartesian section の評価の全境界持ち上げ。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories

/-- 概要：固定始点収縮があれば部分パラメータ上の section を評価を固定して延長できる。
方針：積の和上で輸送を貼り、単射に沿う cocartesian ホモトピーの相対延長を使う。
規約：境界条件と評価条件は同時に、厳密な等式として保持する。
使われ方：評価射の自明 Kan fibration 性。 -/
lemma exists_kanSectionTransport_relative_of_fixedPrism {A T E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (a : A ⟶ B) (v : A _⦋0⦌)
    (hC : ∃ C : (Δ[1] : SSet.{u}) ⊗ A ⟶ A,
      prismEndpoint 0 A ≫ C = SSet.const v ∧ prismEndpoint 1 A ≫ C = 𝟙 A ∧
      ∀ K : SSet.{u}, (Δ[1] ◁ (SSet.const v : K ⟶ A)) ≫ C = SSet.const v)
    (U : T.Subcomplex) (f : T ⟶ E)
    (hf : f ≫ p = SSet.const (a.app (Opposite.op ⦋0⦌) v))
    (G : A ⊗ (U : SSet.{u}) ⟶ E) (hGp : G ≫ p = fst A (U : SSet.{u}) ≫ a)
    (hGi : lift (SSet.const v) (𝟙 (U : SSet.{u})) ≫ G = U.ι ≫ f)
    (hGc : ∀ (x : (U : SSet.{u}) _⦋0⦌) (e : A _⦋1⦌), IsCocartesianEdge p
      (G.app (Opposite.op ⦋1⦌) (e, PinchedHom.constant x 1))) :
    ∃ F : A ⊗ T ⟶ E,
      F ≫ p = fst A T ≫ a ∧ (A ◁ U.ι) ≫ F = G ∧
      lift (SSet.const v) (𝟙 T) ≫ F = f ∧
      ∀ (x : T _⦋0⦌) (e : A _⦋1⦌), IsCocartesianEdge p
        (F.app (Opposite.op ⦋1⦌) (e, PinchedHom.constant x 1)) := by
  have : CocartesianHornFibration p := CocartesianFibration.toCocartesianHornFibration p
  have : Quasicategory E := quasicategory_of_innerFibration p
  obtain ⟨C, hC₀, hC₁, hCv⟩ := hC
  let S := SerrePositivity.InfinityCategories.sectionVertexSpan v
  let V := Subcomplex.unionProd S U
  let q := Subcomplex.unionProd.isPushout S U
  have hV₁ : Subcomplex.unionProd.ι₁ S U ≫ V.ι = A ◁ U.ι :=
    Subcomplex.unionProd.ι₁_ι S U
  have hV₂ : Subcomplex.unionProd.ι₂ S U ≫ V.ι = S.ι ▷ T :=
    Subcomplex.unionProd.ι₂_ι S U
  let f₀ : A ⊗ T ⟶ E := snd A T ≫ f
  let β : (Δ[1] : SSet.{u}) ⊗ (A ⊗ T) ⟶ B := (Δ[1] ◁ fst A T) ≫ C ≫ a
  let H₁ := SerrePositivity.InfinityCategories.sectionPrism C (U : SSet.{u}) ≫ G
  let H₂ : (Δ[1] : SSet.{u}) ⊗ ((S : SSet.{u}) ⊗ T) ⟶ E :=
    snd Δ[1] _ ≫ snd (S : SSet.{u}) T ≫ f
  have hSG : (S.ι ▷ (U : SSet.{u})) ≫ G = snd (S : SSet.{u}) _ ≫ U.ι ≫ f := by
    have hi : S.ι ▷ (U : SSet.{u}) =
        snd (S : SSet.{u}) _ ≫ lift (SSet.const v) (𝟙 (U : SSet.{u})) := by
      dsimp only [S]
      rw [SerrePositivity.InfinityCategories.sectionVertexSpan_ι]
      rfl
    rw [hi, Category.assoc, hGi]
  have hglue : (Δ[1] ◁ (S.ι ▷ (U : SSet.{u}))) ≫ H₁ =
      (Δ[1] ◁ ((S : SSet.{u}) ◁ U.ι)) ≫ H₂ := by
    dsimp only [H₁]
    rw [← Category.assoc, SerrePositivity.InfinityCategories.sectionPrism_vertex v C hCv, Category.assoc, hSG]
    rfl
  have hc₁ : ∀ x : (A ⊗ (U : SSet.{u})) _⦋0⦌, HasCocartesianHornLifting p (edgeOfSimplex
      (H₁.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) := by
    intro x
    exact (isCocartesianEdge_iff_hasCocartesianHornLifting p _).1
      (hGc x.2 (C.app _ (SSet.yonedaEquiv (𝟙 Δ[1]), PinchedHom.constant x.1 1)))
  have hc₂ : ∀ x : ((S : SSet.{u}) ⊗ T) _⦋0⦌, HasCocartesianHornLifting p (edgeOfSimplex
      (H₂.app (Opposite.op ⦋1⦌)
        (SSet.yonedaEquiv (𝟙 (Δ[1] : SSet.{u})), PinchedHom.constant x 1))) := by
    intro x
    have hi := isEquivalencePathVertex_const x
    unfold IsEquivalencePathVertex at hi
    rw [intervalFunctorVertexEdge_functorVertex] at hi
    exact (hi.map (snd (S : SSet.{u}) T ≫ f)).hasCocartesianHornLifting p
  obtain ⟨J, hJ₁, hJ₂, hJc⟩ := exists_kanCocartesianHomotopy_unionProd p S U H₁ H₂ hglue hc₁ hc₂
  have hz₁ : prismEndpoint 0 (A ⊗ (U : SSet.{u})) ≫ H₁ = (A ◁ U.ι) ≫ f₀ := by
    dsimp only [H₁, f₀]
    rw [← Category.assoc, SerrePositivity.InfinityCategories.sectionPrism_zero v C hC₀, Category.assoc, hGi]
    rw [← Category.assoc (A ◁ U.ι), whiskerLeft_snd, Category.assoc]
  have hz₂ : prismEndpoint 0 ((S : SSet.{u}) ⊗ T) ≫ H₂ = (S.ι ▷ T) ≫ f₀ := by
    dsimp only [H₂, f₀]
    rw [← Category.assoc, prismEndpoint_snd, Category.id_comp,
      ← Category.assoc, whiskerRight_snd]
  have hp₁ : H₁ ≫ p = (Δ[1] ◁ (A ◁ U.ι)) ≫ β := by
    dsimp only [H₁, β, SerrePositivity.InfinityCategories.sectionPrism]
    rw [Category.assoc, hGp, ← Category.assoc, lift_fst,
      ← Category.assoc, ← whiskerLeft_comp, whiskerLeft_fst]
    rw [Category.assoc]
  have hp₂ : H₂ ≫ p = (Δ[1] ◁ (S.ι ▷ T)) ≫ β := by
    dsimp only [H₂, β]
    rw [Category.assoc, Category.assoc, hf, SSet.comp_const, SSet.comp_const,
      ← Category.assoc, ← whiskerLeft_comp, whiskerRight_fst]
    dsimp only [S]
    rw [SerrePositivity.InfinityCategories.sectionVertexSpan_ι, SSet.comp_const,
      ← Category.assoc (Δ[1] ◁ (SSet.const v : _ ⟶ A)), hCv _, SSet.const_comp]
  have hJ₀ : prismEndpoint 0 (V : SSet.{u}) ≫ J = V.ι ≫ f₀ := by
    apply q.hom_ext
    · rw [← Category.assoc, ← prismEndpoint_naturality, Category.assoc, hJ₁, hz₁]
      rw [← Category.assoc (Subcomplex.unionProd.ι₁ S U), hV₁]
    · rw [← Category.assoc, ← prismEndpoint_naturality, Category.assoc, hJ₂, hz₂]
      rw [← Category.assoc (Subcomplex.unionProd.ι₂ S U), hV₂]
  have hJp : J ≫ p = (Δ[1] ◁ V.ι) ≫ β := by
    apply curry_injective
    apply q.hom_ext
    · rw [← curry_natural_left, ← Category.assoc, hJ₁, hp₁, ← curry_natural_left]
      rw [← Category.assoc (Δ[1] ◁ Subcomplex.unionProd.ι₁ S U),
        ← whiskerLeft_comp, hV₁]
    · rw [← curry_natural_left, ← Category.assoc, hJ₂, hp₂, ← curry_natural_left]
      rw [← Category.assoc (Δ[1] ◁ Subcomplex.unionProd.ι₂ S U),
        ← whiskerLeft_comp, hV₂]
  have hf₀ : f₀ ≫ p = prismEndpoint 0 (A ⊗ T) ≫ β := by
    dsimp only [f₀, β]
    rw [Category.assoc, hf, SSet.comp_const, ← Category.assoc,
      prismEndpoint_naturality, Category.assoc, ← Category.assoc (prismEndpoint 0 A), hC₀,
      SSet.const_comp, SSet.comp_const]
  obtain ⟨H, hHV, hH₀, hHp, hHc⟩ := cocartesianHomotopy_extend p V.ι J f₀ β hJ₀ hf₀ hJp hJc
  have hHb : (Δ[1] ◁ (A ◁ U.ι)) ≫ H = H₁ := by
    rw [← Subcomplex.unionProd.ι₁_ι S U, whiskerLeft_comp, Category.assoc, hHV, hJ₁]
  have hHs : (Δ[1] ◁ (S.ι ▷ T)) ≫ H = H₂ := by
    rw [← Subcomplex.unionProd.ι₂_ι S U, whiskerLeft_comp, Category.assoc, hHV, hJ₂]
  let F := prismEndpoint 1 (A ⊗ T) ≫ H
  have hFp : F ≫ p = fst A T ≫ a := by
    dsimp only [F]
    rw [Category.assoc, hHp]
    dsimp only [β]
    rw [← Category.assoc, prismEndpoint_naturality, Category.assoc,
      ← Category.assoc (prismEndpoint 1 A), hC₁, Category.id_comp]
  have hFb : (A ◁ U.ι) ≫ F = G := by
    dsimp only [F]
    rw [← Category.assoc, ← prismEndpoint_naturality, Category.assoc, hHb]
    dsimp only [H₁]
    rw [← Category.assoc, SerrePositivity.InfinityCategories.sectionPrism_one C hC₁, Category.id_comp]
  have hFs : (S.ι ▷ T) ≫ F = snd (S : SSet.{u}) T ≫ f := by
    dsimp only [F]
    rw [← Category.assoc, ← prismEndpoint_naturality, Category.assoc, hHs]
    dsimp only [H₂]
    rw [← Category.assoc, prismEndpoint_snd, Category.id_comp]
  have hFi : lift (SSet.const v) (𝟙 T) ≫ F = f := by
    rw [← SerrePositivity.InfinityCategories.sectionVertexParameter_ι v, Category.assoc, hFs]
    rfl
  refine ⟨F, hFp, hFb, hFi, ?_⟩
  intro x e
  let j : (Δ[1] : SSet.{u}) ⟶ A ⊗ T := lift (SSet.yonedaEquiv.symm e) (SSet.const x)
  have hs : j ≫ prismEndpoint 0 (A ⊗ T) ≫ H =
      SSet.const (f.app (Opposite.op ⦋0⦌) x) := by
    rw [hH₀]
    dsimp only [j, f₀]
    rw [← Category.assoc, lift_snd, SSet.const_comp]
  have hc := SerrePositivity.InfinityCategories.cocartesianHomotopy_targetEdge p H j
    (by rw [hs]; exact isCocartesianEdge_constant p _)
    (fun y ↦ (isCocartesianEdge_iff_hasCocartesianHornLifting p _).2 (hHc y))
  change IsCocartesianEdge p (F.app (Opposite.op ⦋1⦌)
    ((SSet.yonedaEquiv.symm e).app _ (SSet.yonedaEquiv (𝟙 Δ[1])),
      PinchedHom.constant x 1)) at hc
  simpa only [SSet.yonedaEquiv_symm_app_id] using hc

/-- 概要：始対象からの相対輸送は境界と評価を同時に固定する。
方針：始対象を固定する収縮を構成して、固定 prism による相対延長へ渡す。
規約：部分パラメータは任意の部分複体。
使われ方：始対象での section の評価の持ち上げ。 -/
lemma exists_kanInitialSectionTransport_relative {A T E B : SSet.{u}} [Quasicategory B]
    (p : E ⟶ B) [CocartesianFibration p] (a : A ⟶ B) (v : A _⦋0⦌)
    (hv : IsInitialVertex v) (U : T.Subcomplex) (f : T ⟶ E)
    (hf : f ≫ p = SSet.const (a.app (Opposite.op ⦋0⦌) v))
    (G : A ⊗ (U : SSet.{u}) ⟶ E) (hGp : G ≫ p = fst A (U : SSet.{u}) ≫ a)
    (hGi : lift (SSet.const v) (𝟙 (U : SSet.{u})) ≫ G = U.ι ≫ f)
    (hGc : ∀ (x : (U : SSet.{u}) _⦋0⦌) (e : A _⦋1⦌), IsCocartesianEdge p
      (G.app (Opposite.op ⦋1⦌) (e, PinchedHom.constant x 1))) :
    ∃ F : A ⊗ T ⟶ E,
      F ≫ p = fst A T ≫ a ∧ (A ◁ U.ι) ≫ F = G ∧
      lift (SSet.const v) (𝟙 T) ≫ F = f ∧
      ∀ (x : T _⦋0⦌) (e : A _⦋1⦌), IsCocartesianEdge p
        (F.app (Opposite.op ⦋1⦌) (e, PinchedHom.constant x 1)) :=
  exists_kanSectionTransport_relative_of_fixedPrism p a v hv.exists_fixed_initial_prism
    U f hf G hGp hGi hGc

end SerrePositivity.InfinityCategories
