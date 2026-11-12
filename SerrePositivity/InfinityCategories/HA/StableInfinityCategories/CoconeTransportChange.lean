module
public import SerrePositivity.InfinityCategories.HA.StableInfinityCategories.CoconeEndpointTransport

/-! # 余錐輸送の図式表示の変更と展開

概要：等しい固定図式への輸送は、fiber の射と展開した区間族の両方で表示変更と整合する。
方針：図式の等号の帰納法と coslice 制限の uncurry の式を使う。
規約：終点の辺は固定。使われ方：対称 span の二枝を同じ辺に揃えて貼る。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits MonoidalCategory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：等しい固定図式へ余錐空間の終点輸送を移す。
方針：図式の等号で輸送のデータ全体を置き換える。
規約：底の辺とその向きは保つ。使われ方：対称 span の両枝の表示を揃える。 -/
def LeftFibrationFiberTransport.changeDiagram {K X : SSet.{u}} {p q : K ⟶ X}
    {x y : X _⦋0⦌} {a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) a) (h : p = q) :
    _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection q) a := h ▸ T

/-- 概要：表示変更した輸送の射は、両端の fiber の表示変更と可換。
方針：図式の等号を消す。
規約：変更後から元の表示へ戻す向きの式。使われ方：両枝での終端の射の正規化。 -/
lemma LeftFibrationFiberTransport.changeDiagram_map {K X : SSet.{u}} {p q : K ⟶ X}
    {x y : X _⦋0⦌} {a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) a) (h : p = q) :
    (T.changeDiagram h).map ≫ eqToHom (congrArg (fun p => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p y) h.symm) =
      eqToHom (congrArg (fun p => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p x) h.symm) ≫ T.map := by
  subst q
  simp only [changeDiagram, eqToHom_refl, Category.comp_id, Category.id_comp]

/-- 概要：表示変更した輸送の区間族を展開すると、入力の表示変更を元へ戻した族になる。
方針：図式の等号の帰納法で恒等の表示変更に戻す。
規約：入力族のパラメーター Z は任意。使われ方：二枝の貼り合わせ条件の共通表示への帰着。 -/
lemma LeftFibrationFiberTransport.changeDiagram_uncurry {K X Z : SSet.{u}} {p q : K ⟶ X}
    {x y : X _⦋0⦌} {a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y}
    (T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) a) (h : p = q)
    (v : Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace q x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry ((v ▷ (Δ[1] : SSet.{u})) ≫ (T.changeDiagram h).h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (((v ≫ eqToHom (congrArg (fun p => _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p x) h.symm)) ▷
        (Δ[1] : SSet.{u})) ≫ T.h) := by
  subst q
  simp only [changeDiagram, eqToHom_refl, Category.comp_id]

/-- 概要：制限と整合する輸送の区間族を共通部分へ展開すると、制限した入力の輸送族になる。
方針：coslice の uncurry の制限則と、パラメーターの二段階の前合成をまとめる。
規約：区間族の制限可換性を入力とし、充填性は不要。使われ方：二枝の共通始点での一致。 -/
lemma coconeEndpointTransport_restrict_uncurry {K L X Z : SSet.{u}}
    (p : K ⟶ X) (i : L ⟶ K) {x y : X _⦋0⦌}
    (a : SSet.Truncated.Edge (X := (truncation 2).obj X) x y)
    (T : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection p) a)
    (S : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.LeftFibrationFiberTransport (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderProjection (i ≫ p)) a)
    (h : T.h ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderRestrict p i =
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p i x ▷ (Δ[1] : SSet.{u})) ≫ S.h)
    (v : Z ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.LimitsAndColimits.coconeMappingSpace p x) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 (Z ⊗ (Δ[1] : SSet.{u}))) ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry ((v ▷ (Δ[1] : SSet.{u})) ≫ T.h) =
      _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry (((v ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.cosliceRestrictionFiberMap p i x) ▷ (Δ[1] : SSet.{u})) ≫ S.h) := by
  rw [← _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceUnderUncurry_restrict, Category.assoc, h, ← Category.assoc, ← comp_whiskerRight]

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
