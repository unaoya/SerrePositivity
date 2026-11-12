module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.PrismFilling
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap

/-!
概要：先頭の単体と境界の prism からの延長。
方針：先頭と境界を pushout で貼り、可逆な垂直辺による prism の延長を使う。
規約：一方の端点の単体を厳密に固定する。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM） の同値の path の持ち上げ。

対応節は Kerodon 4.5（Tag 01DE）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence

/-- 概要：先頭の一次ホーンの唯一の頂点。
方針：標準辺の始点は一を値に取らない。
規約：周囲の頂点番号は零。
使われ方：Kerodon §4.5.3（Tag 032Y） の prism の先頭への制限。 -/
def hornOneFirstVertex : (horn 1 0 : SSet.{u}) _⦋0⦌ :=
  ⟨stdSimplex.obj₀Equiv.symm 0, by
    apply (mem_horn_iff_notMem_range _ (0 : Fin 2)).2
    refine ⟨1, by decide, ?_⟩
    rintro ⟨i, hi⟩
    exact (by decide : (0 : Fin 2) ≠ 1) hi⟩

/-- 概要：先頭の一次ホーンの prism の切断。
方針：先頭のホーン頂点への定値射と恒等射を組にする。
規約：任意の始域を扱う。
使われ方：Kerodon §4.5.3（Tag 032Y） の prism の先頭の固定。 -/
noncomputable def hornOneFirstSection (A : SSet.{u}) : A ⟶ (horn 1 0 : SSet.{u}) ⊗ A :=
  lift (SSet.const hornOneFirstVertex) (𝟙 A)

/-- 概要：先頭のホーンの切断を含めると prism の先頭の端点。
方針：部分型の値を取る。
規約：時刻零の射。
使われ方：Kerodon §4.5.3（Tag 032Y） の端点の回収。 -/
lemma hornOneFirstSection_ι (A : SSet.{u}) :
    hornOneFirstSection A ≫ ((horn 1 0).ι ▷ A) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 A := rfl

/-- 概要：先頭のホーンの切断の第二成分は恒等射。
方針：組の第二成分を取る。
規約：任意の始域。
使われ方：Kerodon §4.5.3（Tag 032Y） の端点の回収。 -/
lemma hornOneFirstSection_snd (A : SSet.{u}) :
    hornOneFirstSection A ≫ snd (horn 1 0 : SSet.{u}) A = 𝟙 A := rfl

/-- 概要：境界の最初の頂点上の垂直辺。
方針：標準区間の恒等一単体と境界の最初の頂点の定値一単体を組にする。
規約：境界の標準単体の次元は n+1。
使われ方：Kerodon §4.5.3（Tag 032Y） の可逆性を確認する辺。 -/
def prismBoundaryFirstVerticalEdge (n : ℕ) :
    ((Δ[1] : SSet.{u}) ⊗ (boundary (n + 1) : SSet.{u})) _⦋1⦌ :=
  ⟨SSet.yonedaEquiv (𝟙 Δ[1]),
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (X := (boundary (n + 1) : SSet.{u}))
      ⟨stdSimplex.obj₀Equiv.symm 0, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩ 1⟩

/-- 概要：境界の最初の垂直辺を含めると prism の固定した最初の垂直辺。
方針：境界包含が定値単体を定値単体へ写すことを使う。
規約：先頭と境界の和の部分複体への包含。
使われ方：Kerodon §4.5.3（Tag 032Y） の prism の延長。 -/
lemma prismBoundaryFirstVerticalEdge_ι₁ (n : ℕ) :
    (Subcomplex.unionProd.ι₁ (horn 1 0) (boundary (n + 1))).app (Opposite.op ⦋1⦌)
      (prismBoundaryFirstVerticalEdge n) =
        ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge_mem n⟩ := by
  apply Subtype.ext
  apply Prod.ext
  · rfl
  · exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedConstant_map (boundary (n + 1)).ι
      ⟨stdSimplex.obj₀Equiv.symm 0, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.vertex_mem_boundary n 0⟩ 1

/-- 概要：先頭の単体と境界上の prism は、最初の垂直辺が可逆なら厳密に延長できる。
方針：二つの射を pushout で貼り、prism の延長を取り両制限を確認する。
規約：先頭の端点と境界の prism の両方を固定する。
使われ方：Kerodon Corollary 4.5.3.24（Tag 02VM） の同値の path の持ち上げ。 -/
lemma prism_extend_boundary_with_endpoint {Y : SSet.{u}} [Quasicategory Y] (n : ℕ)
    (H : (Δ[1] : SSet.{u}) ⊗ (boundary (n + 1) : SSet.{u}) ⟶ Y)
    (F₀ : (Δ[n + 1] : SSet.{u}) ⟶ Y)
    (hF₀ : (boundary (n + 1)).ι ≫ F₀ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 (boundary (n + 1) : SSet.{u}) ≫ H)
    (hH : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.IsInvertibleEdge (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.edgeOfSimplex (H.app (Opposite.op ⦋1⦌)
      (prismBoundaryFirstVerticalEdge n)))) :
    ∃ F : (Δ[1] : SSet.{u}) ⊗ Δ[n + 1] ⟶ Y,
      (Δ[1] ◁ (boundary (n + 1)).ι) ≫ F = H ∧ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismEndpoint 0 Δ[n + 1] ≫ F = F₀ := by
  let S := horn.{u} 1 0
  let T := boundary.{u} (n + 1)
  let q := Subcomplex.unionProd.isPushout S T
  have hw : (S.ι ▷ (T : SSet.{u})) ≫ H =
      ((S : SSet.{u}) ◁ T.ι) ≫ (snd (S : SSet.{u}) Δ[n + 1] ≫ F₀) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.hornOneFirst_prism_factorization, Category.assoc, ← hF₀]
    rfl
  let a := q.desc H (snd (S : SSet.{u}) Δ[n + 1] ≫ F₀) hw
  have ha₁ : Subcomplex.unionProd.ι₁ S T ≫ a = H := q.inl_desc _ _ _
  have ha₂ : Subcomplex.unionProd.ι₂ S T ≫ a =
      snd (S : SSet.{u}) Δ[n + 1] ≫ F₀ := q.inr_desc _ _ _
  have hv : a.app (Opposite.op ⦋1⦌)
      ⟨_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge (n + 1), _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prismFirstVerticalEdge_mem n⟩ =
        H.app (Opposite.op ⦋1⦌) (prismBoundaryFirstVerticalEdge n) := by
    have h := ConcreteCategory.congr_hom (NatTrans.congr_app ha₁ (Opposite.op ⦋1⦌))
      (prismBoundaryFirstVerticalEdge n)
    change a.app (Opposite.op ⦋1⦌)
      ((Subcomplex.unionProd.ι₁ S T).app (Opposite.op ⦋1⦌)
        (prismBoundaryFirstVerticalEdge n)) = _ at h
    rw [prismBoundaryFirstVerticalEdge_ι₁] at h
    exact h
  obtain ⟨F, hF⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.prism_exists_extension_of_invertible_firstEdge n a
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.isInvertibleEdge_congr hv).mpr hH)
  refine ⟨F, ?_, ?_⟩
  · rw [← Subcomplex.unionProd.ι₁_ι S T, Category.assoc, hF, ha₁]
  · have h : (S.ι ▷ (Δ[n + 1] : SSet.{u})) ≫ F =
        snd (S : SSet.{u}) Δ[n + 1] ≫ F₀ := by
      rw [← Subcomplex.unionProd.ι₂_ι S T, Category.assoc, hF, ha₂]
    have h' := congrArg (fun f ↦ hornOneFirstSection (Δ[n + 1] : SSet.{u}) ≫ f) h
    dsimp only [S] at h'
    simpa only [← Category.assoc, hornOneFirstSection_ι, hornOneFirstSection_snd,
      Category.id_comp] using h'

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence
