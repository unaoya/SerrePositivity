module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceKan
public import SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.TerminalMap
public import Mathlib.Tactic.CrossRefAttribute

/-!
概要：全境界の充填による可縮な Kan 複体の条件。
方針：点への射が trivial Kan fibration であることと比較し、非空性と連結性を導く。
規約：零次元の境界も含み、単なる π₀ の自明性とは区別する。
使われ方：HTT Proposition 1.2.12.4、Kerodon Proposition 4.4.2.14（Tag 01NU）。

対応節は Kerodon 1.5（Tag 0055）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories

/-- 概要：可縮な Kan 複体の境界充填条件。
方針：全ての境界の射の延長を要求する。
規約：n=0 も含めて非空性を含む。
使われ方：HTT Proposition 1.2.12.4、Kerodon Definition 1.5.5.8（Tag 0072） の可縮な Kan 複体。 -/
@[kerodon 0072]
def IsContractibleKan (K : SSet.{u}) : Prop :=
  ∀ (n : ℕ) (b : (boundary n : SSet.{u}) ⟶ K),
    ∃ F : (Δ[n] : SSet.{u}) ⟶ K, (boundary n).ι ≫ F = b

/-- 概要：可縮な Kan 複体の条件は点への射が trivial Kan fibration であることと同値。
方針：A2 の全境界による rlp の判定を使う。
規約：標的は Mathlib の選択された終対象。
使われ方：Kerodon Proposition 4.4.2.14（Tag 01NU） の fiber の可縮性。 -/
@[kerodon 0072, kerodon 0075]
lemma isContractibleKan_iff_trivialKanFibration (K : SSet.{u}) :
    IsContractibleKan K ↔ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.TrivialKanFibration (terminal.from K) := by
  rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.trivialKanFibration_iff_boundary]
  constructor
  · intro h n
    constructor
    intro b c sq
    obtain ⟨F, hF⟩ := h n b
    exact CommSq.HasLift.mk' { l := F, fac_left := hF, fac_right := terminal.hom_ext _ _ }
  · intro h n b
    have := h n
    have sq : CommSq b (boundary n).ι (terminal.from K) (terminal.from (Δ[n] : SSet.{u})) :=
      ⟨terminal.hom_ext _ _⟩
    exact ⟨sq.lift, sq.fac_left⟩

/-- 概要：全境界を充填できる単体集合は非空。
方針：空の零次境界の充填を取る。
規約：非空性は零単体の型の非空性。
使われ方：HTT Proposition 1.2.12.9 の終対象の列の非空性。 -/
lemma IsContractibleKan.nonempty {K : SSet.{u}} (h : IsContractibleKan K) : Nonempty (K _⦋0⦌) := by
  let b : (boundary 0 : SSet.{u}) ⟶ K := by
    rw [boundary_zero]
    exact Subcomplex.isInitialBot.to K
  obtain ⟨F, _⟩ := h 0 b
  exact ⟨SSet.yonedaEquiv F⟩

/-- 概要：全境界を充填できる単体集合は Kan 複体。
方針：点への射の全単射の rlp をホーン包含に適用する。
規約：追加の quasicategory 性を前提にしない。
使われ方：HTT Proposition 1.2.12.4、可縮性の条件に含まれる Kan 性。 -/
@[kerodon 0076]
lemma IsContractibleKan.kanComplex {K : SSet.{u}} (h : IsContractibleKan K) : KanComplex K := by
  have ht := (isContractibleKan_iff_trivialKanFibration K).1 h
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.kanComplex_of_rightHornFillers
  intro n i hi σ
  have := ht.mem (horn (n + 1) i).ι inferInstance
  have sq : CommSq σ (horn (n + 1) i).ι (terminal.from K)
      (terminal.from (Δ[n + 1] : SSet.{u})) := ⟨terminal.hom_ext _ _⟩
  exact ⟨sq.lift, sq.fac_left⟩

/-- 概要：可縮な Kan 複体の任意の頂点は終対象。
方針：指定した最後の頂点の条件を保ったまま全境界の充填を適用する。
規約：この方向では quasicategory 性も不要。
使われ方：Kerodon Corollary 4.7.3.13（Tag 02HJ）、HTT §1.2.12。 -/
lemma IsContractibleKan.isTerminalVertex {K : SSet.{u}} (h : IsContractibleKan K)
    (x : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x := fun n b _ ↦ h (n + 1) b

/-- 概要：可縮な Kan 複体の任意の頂点は始対象。
方針：指定した最初の頂点の条件を保ったまま全境界の充填を適用する。
規約：この方向では quasicategory 性も不要。
使われ方：Kerodon Corollary 4.7.3.13（Tag 02HJ） の双対、HTT §1.2.12。 -/
lemma IsContractibleKan.isInitialVertex {K : SSet.{u}} (h : IsContractibleKan K)
    (x : K _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsInitialVertex x := fun n b _ ↦ h (n + 1) b

/-- 概要：可縮な Kan 複体の連結成分の型は高々一点。
方針：任意の二頂点の間に終対象性による辺を取り、同じ連結成分であることを示す。
規約：非空性は別の補題で与える。
使われ方：HTT §1.2.12、写像空間の可縮性から通常の終対象性へ。 -/
lemma IsContractibleKan.piZero_subsingleton {K : SSet.{u}} (h : IsContractibleKan K) :
    Subsingleton (SSet.π₀ K) := by
  constructor
  intro a b
  obtain ⟨x, rfl⟩ := SSet.π₀.mk_surjective a
  obtain ⟨y, rfl⟩ := SSet.π₀.mk_surjective b
  obtain ⟨e⟩ := (h.isTerminalVertex y).nonempty_edge x
  exact SSet.π₀.sound (SSet.Edge.ofTruncated e)

/-- 概要：非空で全ての頂点が終対象なら全境界を充填できる。
方針：零次境界では頂点を選び、正次数では境界の最後の頂点の終対象性を使う。
規約：全ての頂点が終対象という条件は元の充填定義のまま。
使われ方：HTT Proposition 1.2.12.9 の終対象の全部分複体。 -/
lemma isContractibleKan_of_nonempty_of_all_terminal {K : SSet.{u}}
    (hne : Nonempty (K _⦋0⦌)) (hterm : ∀ x : K _⦋0⦌, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories.IsTerminalVertex x) :
    IsContractibleKan K := by
  intro n b
  cases n with
  | zero =>
    obtain ⟨x⟩ := hne
    exact ⟨SSet.const x, boundary.hom_ext₀⟩
  | succ n =>
    let x := SSet.yonedaEquiv (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.boundaryVertex n (Fin.last (n + 1)) ≫ b)
    exact hterm x n b (SSet.yonedaEquiv.symm_apply_apply _).symm

/-- 概要：可縮な Kan 複体の条件は同型で不変。
方針：境界を逆同型で戻して充填し、順方向の同型で写す。
規約：任意の単体集合の同型を扱う。
使われ方：HTT Proposition 1.2.12.4 の fiber の模型の比較。 -/
lemma isContractibleKan_of_iso {K L : SSet.{u}} (e : K ≅ L) (h : IsContractibleKan K) :
    IsContractibleKan L := by
  intro n b
  obtain ⟨F, hF⟩ := h n (b ≫ e.inv)
  refine ⟨F ≫ e.hom, ?_⟩
  rw [← Category.assoc, hF, Category.assoc, e.inv_hom_id, Category.comp_id]

end SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.1.3.4"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.isContractibleKan_of_iso
attribute [cite HTT "2.3.4.15" (partial := component) "仮定：k=−2、対象は Kan 複体で、可縮性を全境界の RLP による native IsContractibleKan で指定（Lean の十分条件）。結論：負二次を contractible とする原典の convention の成分を表す。k≥−1 の πi の消滅の一般定義と、SpaceInfinity 上の離散同値で定義した Is0TruncatedSpace との比較は含まない。"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.FunctorsOfInfinityCategories.IsContractibleKan
