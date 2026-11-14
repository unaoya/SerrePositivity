module
public import SerrePositivity.KST.SConstruction.CoreSimplicial

/-! # 有限回反復した S 構成の対象
概要：既存の全 gapped 図式の S 構成を有限回反復し、各対象の core を取る。
方針：次数のリストについて再帰し、quasicategory 性と零対象を移す。
規約：先頭が最も外側の S 構成。多単体的な射と delooping は別に証明する。
使われ方：BGT §7 の反復 S• と reduced な境界条件。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet
open SerrePositivity.InfinityCategories
open scoped Simplicial

/-- 概要：有限リストで指定した次数の反復 S 構成。
方針：先頭の次数を外側の S 構成として再帰する。
規約：空リストでは元の C。使われ方：多重 S 構成の各対象。 -/
def iteratedSConstruction : List ℕ → SSet.{u} → SSet.{u}
  | [], C => C
  | n :: ns, C => sConstruction n (iteratedSConstruction ns C)

/-- 概要：反復 S 構成は quasicategory を保つ。
方針：各段の全部分図式圏の quasicategory 性を帰納的に使う。
規約：安定性は不要。使われ方：反復 core の Kan 性。 -/
instance iteratedSConstruction_quasicategory (ns : List ℕ) (C : SSet.{u}) [Quasicategory C] :
    Quasicategory (iteratedSConstruction ns C) := by
  induction ns with
  | nil => exact inferInstanceAs (Quasicategory C)
  | cons n ns ih =>
    letI := ih
    exact sConstruction_quasicategory n (iteratedSConstruction ns C)

/-- 概要：反復 S 構成は零対象の存在を保つ。
方針：各段の定値零図式を帰納的に使う。
規約：C は零対象を持つ quasicategory。使われ方：反復構成の基点。 -/
instance iteratedSConstruction_hasZeroVertex (ns : List ℕ) (C : SSet.{u}) [Quasicategory C]
    [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex (iteratedSConstruction ns C) := by
  induction ns with
  | nil => exact inferInstanceAs (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C)
  | cons n ns ih =>
    letI := ih
    exact sConstruction_hasZeroVertex n (iteratedSConstruction ns C)

/-- 概要：元の零対象から反復の零図式を指定する。
方針：各段で零図式を作り、その零対象性の証明も保持する。
規約：元の零対象の選択を明示する。使われ方：多重実現の基点。 -/
def iteratedZeroVertex (ns : List ℕ) {C : SSet.{u}} [Quasicategory C]
    (z : C _⦋0⦌) (hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z) : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.ZeroVertex (iteratedSConstruction ns C) :=
  match ns with
  | [] => ⟨z, hz.1, hz.2⟩
  | n :: ns =>
    let v := iteratedZeroVertex ns z hz
    ⟨sConstructionZeroVertex n v.vertex v.isZero,
      (sConstructionZeroVertex_isZero n v.vertex v.isZero).1,
      (sConstructionZeroVertex_isZero n v.vertex v.isZero).2⟩

/-- 概要：反復 S 構成の core。
方針：α2 の core を反復した図式圏へ適用する。
規約：core 自体を S の入力にせず、最後に core を取る。
使われ方：反復 S• による K スペクトルの段の準備。 -/
def iteratedCoreSConstruction (ns : List ℕ) (C : SSet.{u}) : SSet.{u} :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.quasicategoryCore (iteratedSConstruction ns C) : SSet.{u})

/-- 概要：反復 S 構成の core は Kan 複体。
方針：反復後の quasicategory 性と α2 の core の Kan 性を使う。
規約：安定性は不要。使われ方：反復構成の各段の Kan 性。 -/
instance iteratedCoreSConstruction_kanComplex (ns : List ℕ) (C : SSet.{u}) [Quasicategory C] :
    KanComplex (iteratedCoreSConstruction ns C) := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.TheInfinityCategoryQC.quasicategoryCore_kanComplex _

/-- 概要：可縮な Kan 複体を値域とする S_n の全頂点は零対象。
方針：図式圏で点ごとの零対象性を使い、全部分複体へ移す。
規約：全ての gapped 図式を保持する。使われ方：零次数を含む反復の可縮性。 -/
lemma sConstruction_isZeroVertex_of_contractible (n : ℕ) {C : SSet.{u}}
    [Quasicategory C] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan C) (v : (sConstruction n C) _⦋0⦌) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex v := by
  have ha : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex v.val := by
    have he : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.functorVertex (gappedDiagram v) = v.val :=
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.Equivalence.functorVertexEquiv _ C).apply_symm_apply _
    rw [← he]
    apply isZeroVertex_functorVertex_of_pointwise
    intro a
    exact ⟨h.isInitialVertex _, h.isTerminalVertex _⟩
  exact ⟨isInitialVertex_fullSubcomplex_of_ambient _ _ ha.1,
    isTerminalVertex_fullSubcomplex_of_ambient _ _ ha.2⟩

/-- 概要：S_n は可縮な Kan 複体の可縮性を保つ。
方針：定値零図式で非空性を示し、全頂点の終対象性で境界を充填する。
規約：core を取る前の主張。使われ方：反復の零方向の可縮性。 -/
lemma sConstruction_isContractibleKan_of_contractible (n : ℕ) {C : SSet.{u}}
    [Quasicategory C] (h : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan C) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (sConstruction n C) := by
  let z := Classical.choice h.nonempty
  have hz : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.IsZeroVertex z := ⟨h.isInitialVertex z, h.isTerminalVertex z⟩
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_nonempty_of_all_terminal
  · exact ⟨sConstructionZeroVertex n z hz⟩
  · intro v
    exact (sConstruction_isZeroVertex_of_contractible n h v).2

/-- 概要：どれかの次数が零なら反復 S 構成は可縮 Kan 複体。
方針：零次数で S_0 の可縮性を使い、外側の S 構成へ可縮性を移す。
規約：任意の位置の零次数。使われ方：反復構成の reduced な境界条件。 -/
lemma iteratedSConstruction_isContractibleKan_of_zero_mem (ns : List ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] (h : 0 ∈ ns) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (iteratedSConstruction ns C) := by
  induction ns with
  | nil => exact False.elim (List.not_mem_nil h)
  | cons n ns ih =>
    rcases List.mem_cons.mp h with hn | hns
    · subst n
      exact sConstructionZero_isContractibleKan (iteratedSConstruction ns C)
    · exact sConstruction_isContractibleKan_of_contractible n (ih hns)

/-- 概要：零次数を含む反復 S 構成の core は可縮 Kan 複体。
方針：反復図式圏の可縮性を Kan 複体と core の比較同型で移す。
規約：任意の位置の零次数。使われ方：反復実現の基点と境界の比較。 -/
lemma iteratedCoreSConstruction_isContractibleKan_of_zero_mem (ns : List ℕ) (C : SSet.{u})
    [Quasicategory C] [_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.ZeroObjects.HasZeroVertex C] (h : 0 ∈ ns) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan (iteratedCoreSConstruction ns C) := by
  have hc := iteratedSConstruction_isContractibleKan_of_zero_mem ns C h
  letI := hc.kanComplex
  exact _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso (kanCoreIso (iteratedSConstruction ns C)) hc

end SerrePositivity.KST.SConstruction
