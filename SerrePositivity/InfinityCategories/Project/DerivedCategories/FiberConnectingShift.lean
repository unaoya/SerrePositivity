module
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.FiberSquareTriangle

/-! # fiber の接続射と D3 のシフト比較

概要：指定四辺の接続射を h D(S) の D → A[1] の射として読み、D3 のシフト比較と両立させる。
方針：局所化の標準比較と D3 の充満忠実性で接続射を持ち上げる。
規約：整数シフトの既存の CommShift を用いる。使われ方：D6a の接続射の規約の固定。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u w
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories
open CategoryTheory MonoidalCategory DifferentialGraded
open scoped _root_.Simplicial
variable {S : Type u} [CommRing S] [HasDerivedCategory.{w} (ModuleCat.{u} S)]

/-- 概要：D3 の比較の頂点像は同じ複体の導来局所化像に自然に同型である。
方針：複体ホモトピー商と導来局所化の標準比較を評価する。
規約：HasDerivedCategory は D3 と共有する。使われ方：接続射の両端の同定。 -/
def derivedVertexLocalizationIso (x : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S).functor.obj ⟨x⟩ ≅
      DerivedCategory.Q.obj (x.obj 0).val :=
  (DerivedCategory.quotientCompQhIso (ModuleCat S)).app (x.obj 0).val

variable (F : (Δ[1] ⊗ Δ[1] : SSet.{u + 1}) ⟶ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S)

/-- 概要：抽出した cospan の共通終域の D(S) の頂点。
方針：元の終域の semifree 性を付して定値頂点を取る。
規約：型の表記だけを正規化する。使われ方：接続射の始域。 -/
def derivedSquareTargetVertex : (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityCategory S) _⦋0⦌ :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex (⟨(_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation F).targetObj,
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquarePresentation_target F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Semifree S)

/-- 概要：導来圏の接続射を D3 による二頂点の像の間の射に同定する。
方針：始域を局所化像へ、シフトした終域を D3 の像へ戻す。
規約：終域は A の +1 シフト。使われ方：ホモトピー圏へ持ち上げる射。 -/
def derivedSquareConnectingLocalized (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S).functor.obj ⟨derivedSquareTargetVertex F⟩ ⟶
      ((_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S).functor.obj ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex⟩)⟦(1 : ℤ)⟧ :=
  (derivedVertexLocalizationIso (derivedSquareTargetVertex F)).hom ≫
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedSquareFiberTriangle F hF).mor₃ ≫
      ((derivedVertexLocalizationIso (_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex).inv)⟦(1 : ℤ)⟧'

/-- 概要：fiber の接続射を h D(S) の D → A[1] の射として与える。
方針：D3 のシフト比較の逆を合成し、充満忠実な比較関手の逆像を取る。
規約：シフトの整合性は D3 の CommShift を継承する。使われ方：D6a の接続射。 -/
def derivedSquareConnectingHomotopy (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) :
    (⟨derivedSquareTargetVertex F⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S) ⟶
      (⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex⟩ : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyCategory S)⟦(1 : ℤ)⟧ :=
  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S).functor.preimage
    (derivedSquareConnectingLocalized F hF ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalenceShiftIso S 1).inv.app ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex⟩)

/-- 概要：接続射の導来比較像は D3 のシフト同型を通して元の接続射になる。
方針：充満関手の逆像の式とシフト同型の逆則を使う。
規約：同じ指定四辺の接続射を使う。使われ方：長完全列とシフト規約の整合。 -/
lemma derivedSquareConnectingHomotopy_shift (hF : _root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.IsPullbackSquare F) :
    (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalence S).functor.map (derivedSquareConnectingHomotopy F hF) ≫
      (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.derivedInfinityHomotopyEquivalenceShiftIso S 1).hom.app ⟨(_root_.SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.ExamplesOfLimitsAndColimits.pullbackCone F).vertex⟩ =
        derivedSquareConnectingLocalized F hF := by
  rw [derivedSquareConnectingHomotopy, Functor.map_preimage, Category.assoc,
    Iso.inv_hom_id_app]
  exact Category.comp_id _

end SerrePositivity.InfinityCategories.Project.DerivedCategories
