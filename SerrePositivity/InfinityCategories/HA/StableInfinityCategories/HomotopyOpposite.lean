module
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.MappingSpaceLeft

/-! # ホモトピー圏と反対圏の比較

概要：反対の quasicategory のホモトピー圏は元のホモトピー圏の反対と同値である。
方針：辺の反転をホモトピー類へ降ろし、道によるホモトピー圏との比較で挟む。
規約：辺と対象の反転を保つ。使われ方：二項余積から二項積への輸送。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet SSet.Truncated
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.HA.StableInfinityCategories

/-- 概要：反対側の左ホモトピーは辺を元へ戻しても左ホモトピーとなる。
方針：辺の反転の同値と左右ホモトピーの一致を使う。
規約：元の X は quasicategory。使われ方：反転を商へ降ろす。 -/
lemma homotopicL_edgeUnop {X : SSet.{u}} [Quasicategory X] {x y : X.op _⦋0⦌}
    {f g : SSet.Truncated.Edge (X := (truncation 2).obj X.op) x y}
    (h : HomotopicL f g) : HomotopicL (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop (X := X) f) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop (X := X) g) := by
  apply (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homotopicL_edgeOp_iff _ _).1
  exact h

/-- 概要：辺の類のホモトピー圏で辺を元へ戻す反変関手。
方針：辺の反転を商へ降ろし、反転した合成二単体で合成保存を示す。
規約：標的を通常の反対圏とする。使われ方：ホモトピー圏の反対との比較。 -/
def edgeHomotopyUnopFunctor (X : SSet.{u}) [Quasicategory X] :
    HomotopyCategory₂ ((truncation 2).obj X.op) ⥤
      (HomotopyCategory₂ ((truncation 2).obj X))ᵒᵖ where
  obj x := Opposite.op ⟨SSet.opObjEquiv x.pt⟩
  map := Quotient.lift (fun e => (HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop (X := X) e)).op)
    (fun _ _ h => congrArg Quiver.Hom.op
      (homotopicL_edgeUnop h).congr_homotopyCategory₂HomMk)
  map_id x := by
    change (HomotopyCategory₂.homMk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop (X := X) (SSet.Truncated.Edge.id x.pt))).op = _
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.edgeUnop_id]
    rfl
  map_comp := by
    rintro _ _ _ ⟨e⟩ ⟨f⟩
    exact congrArg Quiver.Hom.op
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.compStructUnop (X := X) (Edge.compStruct e f)).homotopyCategory₂_fac.symm)

/-- 概要：辺の反転の関手は充満忠実である。
方針：逆向きの辺の反転を Hom の逆写像に取り、商の代表元上で両逆を確認する。
規約：元の X は quasicategory。使われ方：反対のホモトピー圏の比較同値。 -/
def edgeHomotopyUnopFullyFaithful (X : SSet.{u}) [Quasicategory X] :
    (edgeHomotopyUnopFunctor X).FullyFaithful where
  preimage {x y} f :=
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.homotopyCategory₂OpHomEquiv (X := X) (SSet.opObjEquiv y.pt) (SSet.opObjEquiv x.pt) f.unop
  map_preimage := by
    rintro x y ⟨⟨f⟩⟩
    rfl
  preimage_map := by
    rintro x y ⟨f⟩
    rfl

/-- 概要：反対側の辺の類の圏は元の辺の類の圏の反対と同値である。
方針：充満忠実性に、頂点の反転による本質的全射性を加える。
規約：追加の形状の極限を仮定しない。使われ方：道のホモトピー圏への移行。 -/
def edgeHomotopyUnopEquivalence (X : SSet.{u}) [Quasicategory X] :
    HomotopyCategory₂ ((truncation 2).obj X.op) ≌
      (HomotopyCategory₂ ((truncation 2).obj X))ᵒᵖ := by
  let h := edgeHomotopyUnopFullyFaithful X
  letI := h.full
  letI := h.faithful
  letI : (edgeHomotopyUnopFunctor X).EssSurj :=
    { mem_essImage a := ⟨⟨SSet.opObjEquiv.symm a.unop.pt⟩, ⟨Iso.refl _⟩⟩ }
  letI : (edgeHomotopyUnopFunctor X).IsEquivalence := {}
  exact (edgeHomotopyUnopFunctor X).asEquivalence

/-- 概要：反対の quasicategory のホモトピー圏は元のホモトピー圏の反対と同値である。
方針：辺の類の反転同値を二つの標準比較同値で挟む。
規約：元の X は quasicategory。使われ方：二項余積と二項積の双対化。 -/
def homotopyOppositeEquivalence (X : SSet.{u}) [Quasicategory X] :
    hoFunctor.obj X.op ≌ (hoFunctor.obj X)ᵒᵖ :=
  (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge X.op).symm.trans
    ((edgeHomotopyUnopEquivalence X).trans (_root_.SerrePositivity.InfinityCategories.Kerodon.TheLanguageOfInfinityCategories.InfinityCategories.homotopyCategoryBridge X).op)

end SerrePositivity.InfinityCategories.HA.StableInfinityCategories
