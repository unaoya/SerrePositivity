module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias

public import SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.HomotopyIndexing

/-!
概要：Kan 複体の全基点・全次数でのホモトピー群同型という条件。
方針：構成済みの誘導写像の全単射性で述べる。
規約：零次数は連結成分の全単射。追加の公理や引用を表すクラスではない。
使われ方：Goerss–Jardine I §7、BF 1978 §2、HA §1.4.2。Ω 条件の界面。
-/

@[expose] public section

universe u

open CategoryTheory SSet
open scoped _root_.Simplicial

namespace SerrePositivity.KST.Spectra
end SerrePositivity.KST.Spectra
namespace SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries
open _root_.SerrePositivity.KST.Spectra

variable {X Y Z : SSet.{u}} [KanComplex X] [KanComplex Y] [KanComplex Z]

/-- 概要：全基点・全自然数次数でホモトピー類の誘導写像が全単射である条件。
方針：零次数と正次数を構成済みの共通の界面で表す。
規約：正次数では群準同型の全単射であり、零次数では集合の全単射。
使われ方：BF 1978 §2、Goerss–Jardine I §7。Ω スペクトルの随伴構造写像。 -/
def KanPiIsomorphism (f : X ⟶ Y) : Prop :=
  ∀ (x : X _⦋0⦌) (n : ℕ), Function.Bijective (_root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f (x := x) rfl)

/-- 概要：恒等射は全基点の π_* 同型。
方針：誘導写像の恒等法則を使う。
規約：零次数を含む。
使われ方：BF 1978 §2。Ω 条件の基本例。 -/
theorem KanPiIsomorphism.id (X : SSet.{u}) [KanComplex X] : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (𝟙 X) := by
  intro x n
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (𝟙 X) (x := x) rfl = _root_.id := by
    funext a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_id n a
  rw [h]
  exact Function.bijective_id

/-- 概要：全基点の π_* 同型は合成で閉じる。
方針：ホモトピー類の誘導写像の合成法則と全単射の合成を使う。
規約：中間の基点は最初の写像による像。
使われ方：BF 1978 §2、HA §1.4.2。段の比較の反復。 -/
theorem KanPiIsomorphism.comp {f : X ⟶ Y} {g : Y ⟶ Z}
    (hf : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f) (hg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g) : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f ≫ g) := by
  intro x n
  have h : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f ≫ g) (x := x) rfl =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n g (x := f.app _ x) rfl ∘ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f (x := x) rfl := by
    funext a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n f rfl g rfl rfl a
  rw [h]
  exact (hg (f.app _ x) n).comp (hf x n)

/-- 概要：後の射と合成が全基点 π_* 同型なら、前の射も全基点 π_* 同型。
方針：指定基点での誘導写像の合成を計算し、後の全単射を打ち消す。
規約：零次数を含み、基点の逆像を選ばない方向の打ち消し。
使われ方：BF 1978 §2、HA §1.4.2。置換後の Ω 条件の検証。 -/
theorem KanPiIsomorphism.of_comp {f : X ⟶ Y} {Z : SSet.{u}} [KanComplex Z]
    {g : Y ⟶ Z} (hfg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism (f ≫ g)) (hg : _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism g) :
    _root_.SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries.KanPiIsomorphism f := by
  intro x n
  have heq : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n (f ≫ g) (x := x) rfl =
      _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n g (x := f.app _ x) rfl ∘ _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map n f (x := x) rfl := by
    funext a
    exact _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.HomotopyGroups.KanHomotopy.map_comp n f rfl g rfl rfl a
  have hb := hfg x n
  rw [heq] at hb
  exact hb.of_comp_left (hg (f.app _ x) n).injective

end SerrePositivity.InfinityCategories.Project.KanComplexAuxiliaries

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
