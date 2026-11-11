module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.PinchedSlice
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap

/-!
概要：任意のパラメーターに対する右 pinched 写像空間の普遍性。
方針：slice の頂点上の fiber との同型と join の普遍性を合成する。
規約：左因子を始点に定値、右の一点を終点に固定する。
使われ方：HTT §2.2、Kerodon §4.8.4（Tag 06SQ） の相対的な写像空間の充填。

対応節は Kerodon 4.8（Tag 0578）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors

/-- 概要：写像空間への族を始点の定値面を持つ join の図式へ展開する。
方針：slice の fiber へ移し、slice の普遍性で uncurry する。
規約：右因子は Δ[0]。
使われ方：HTT §2.2 の端点を固定した図式の表示。 -/
noncomputable def pinchedHomUncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ X :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry (f ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x y).hom ≫
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) x)

/-- 概要：展開した図式の左因子は始点に定値。
方針：slice の射影と fiber の固定条件を使う。
規約：任意のパラメーター。
使われ方：HTT §2.2 の pinched 条件。 -/
lemma pinchedHomUncurry_inl {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ≫ pinchedHomUncurry f = SSet.const x := by
  rw [pinchedHomUncurry, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverUncurry_projection, Category.assoc,
    Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberι_comp, SSet.comp_const, SSet.comp_const]

/-- 概要：展開した図式の右因子は終点。
方針：slice の図式を固定する条件を使う。
規約：右因子は標準零単体。
使われ方：HTT §2.2 の固定終点。 -/
lemma pinchedHomUncurry_inr {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ pinchedHomUncurry f = SSet.yonedaEquiv.symm y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_fixed _

/-- 概要：端点を固定した join の図式を右写像空間への族へ戻す。
方針：slice へ curry し、定値の射影により fiber へ持ち上げる。
規約：左因子は始点、右因子は終点に固定する。
使われ方：HTT §2.2 の右写像空間の普遍性。 -/
noncomputable def pinchedHomCurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ X)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ≫ F = SSet.const x)
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ F = SSet.yonedaEquiv.symm y) : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) x (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry F hy)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverCurry_projection F hy).trans hx) ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x y).inv

/-- 概要：図式を curry して uncurry すると元の図式。
方針：fiber の包含と slice の curry の両逆の等式を使う。
規約：固定条件の証明の選択は結果に影響しない。
使われ方：HTT §2.2 の普遍性の往復。 -/
lemma pinchedHomUncurry_curry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ X)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ≫ F = SSet.const x)
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ F = SSet.yonedaEquiv.symm y) :
    pinchedHomUncurry (pinchedHomCurry F hx hy) = F := by
  unfold pinchedHomUncurry pinchedHomCurry
  simp only [Category.assoc, Iso.inv_hom_id_assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift_ι, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_curry]

/-- 概要：写像空間の族は展開した図式で決まる。
方針：slice の uncurry の単射性と fiber の包含の単射性を使う。
規約：任意のパラメーター。
使われ方：HTT §2.2 の端点を固定した族の比較。 -/
lemma pinchedHomUncurry_injective {A X : SSet.{u}} (x y : X _⦋0⦌) :
    Function.Injective (pinchedHomUncurry (A := A) (x := x) (y := y)) := by
  intro f g h
  apply (cancel_mono (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x y).hom).1
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_hom_ext (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) x
  have h' := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_injective (SSet.yonedaEquiv.symm y) h
  simpa only [Category.assoc] using h'

/-- 概要：族を uncurry して curry すると元の族。
方針：uncurry の単射性と図式の往復の等式を使う。
規約：左右の制限は既存の補題で与える。
使われ方：HTT §2.2 の普遍性の逆方向。 -/
lemma pinchedHomCurry_uncurry {A X : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :
    pinchedHomCurry (pinchedHomUncurry f) (pinchedHomUncurry_inl f) (pinchedHomUncurry_inr f) = f := by
  apply pinchedHomUncurry_injective x y
  exact pinchedHomUncurry_curry _ _ _

/-- 概要：図式への展開はパラメーターの前合成と可換。
方針：slice の uncurry の自然性を使う。
規約：右の終点の因子は固定する。
使われ方：HTT §2.2 の境界への制限。 -/
lemma pinchedHomUncurry_precomp {A C X : SSet.{u}} {x y : X _⦋0⦌}
    (i : A ⟶ C) (f : C ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) :
    pinchedHomUncurry (i ≫ f) = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap i (𝟙 Δ[0]) ≫ pinchedHomUncurry f := by
  unfold pinchedHomUncurry
  rw [Category.assoc, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverUncurry_precomp]

/-- 概要：slice の fiber から pinched 模型への同型の逆は単体の明示的な逆構成。
方針：順方向へ含めた後の等式を同型の逆で戻す。
規約：任意の単体集合の任意の次数。
使われ方：HTT §2.2 の curry の標的への自然性。 -/
lemma pinchedHomSliceFiberIso_inv_app {X : SSet.{u}} (x y : X _⦋0⦌) {n : ℕ}
    (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) x) _⦋n⦌) :
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x y).inv.app (Opposite.op ⦋n⦌) s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fiberSimplexToPinched s := by
  have hs : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x y).hom.app (Opposite.op ⦋n⦌)
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fiberSimplexToPinched s) = s := by
    apply Subtype.ext
    apply Subtype.ext
    change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).hom ≫ SSet.yonedaEquiv.symm
      (SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫ s.val.val)) = s.val.val
    rw [Equiv.symm_apply_apply, Iso.hom_inv_id_assoc]
  calc
    _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x y).inv.app (Opposite.op ⦋n⦌)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x y).hom.app (Opposite.op ⦋n⦌) (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fiberSimplexToPinched s)) :=
      congrArg ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x y).inv.app (Opposite.op ⦋n⦌)) hs.symm
    _ = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.fiberSimplexToPinched s := ConcreteCategory.congr_hom
      (NatTrans.congr_app (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x y).hom_inv_id (Opposite.op ⦋n⦌)) _

/-- 概要：端点を固定した curry は標的の射との後合成と可換。
方針：明示的な逆構成を用いて Yoneda 表示の後合成を比較する。
規約：像の端点の固定条件の証明は任意。
使われ方：HTT §2.2 の写像空間の射の充填。 -/
lemma pinchedHomCurry_postcomp {A X Y : SSet.{u}} {x y : X _⦋0⦌}
    (F : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.join A (Δ[0] : SSet.{u}) ⟶ X)
    (hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ≫ F = SSet.const x)
    (hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ F = SSet.yonedaEquiv.symm y) (p : X ⟶ Y)
    (hx' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ≫ (F ≫ p) = SSet.const (p.app (Opposite.op ⦋0⦌) x))
    (hy' : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ (F ≫ p) = SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) y)) :
    pinchedHomCurry F hx hy ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y = pinchedHomCurry (F ≫ p) hx' hy' := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro a
  change (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y).app (Opposite.op ⦋n⦌)
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso x y).inv.app (Opposite.op ⦋n⦌)
      ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiberLift (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverProjection (SSet.yonedaEquiv.symm y)) x (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.sliceOverCurry F hy)
        ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.sliceOverCurry_projection F hy).trans hx)).app (Opposite.op ⦋n⦌) a)) = _
  rw [pinchedHomSliceFiberIso_inv_app]
  unfold pinchedHomCurry
  change _ = (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomSliceFiberIso _ _).inv.app (Opposite.op ⦋n⦌) _
  rw [pinchedHomSliceFiberIso_inv_app]
  apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
  change p.app (Opposite.op ⦋n + 1⦌) (SSet.yonedaEquiv
    ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫ (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 Δ[0]) ≫ F))) =
    SSet.yonedaEquiv ((_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinStdSimplexIso n 0).inv ≫
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinMap (SSet.yonedaEquiv.symm a) (𝟙 Δ[0]) ≫ (F ≫ p)))
  rw [← SSet.yonedaEquiv_comp, Category.assoc, Category.assoc]

/-- 概要：族の join の図式への展開は標的への後合成と可換。
方針：curry の自然性を uncurry し、両逆の等式を使う。
規約：両端も標的の射で移す。
使われ方：HTT §2.2 の持ち上げ問題の展開。 -/
lemma pinchedHomUncurry_postcomp {A X Y : SSet.{u}} {x y : X _⦋0⦌}
    (f : A ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) (p : X ⟶ Y) :
    pinchedHomUncurry (f ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y) = pinchedHomUncurry f ≫ p := by
  have hx : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInl A Δ[0] ≫ (pinchedHomUncurry f ≫ p) =
      SSet.const (p.app (Opposite.op ⦋0⦌) x) := by
    rw [← Category.assoc, pinchedHomUncurry_inl, SSet.const_comp]
  have hy : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.joinInr A Δ[0] ≫ (pinchedHomUncurry f ≫ p) =
      SSet.yonedaEquiv.symm (p.app (Opposite.op ⦋0⦌) y) := by
    rw [← Category.assoc, pinchedHomUncurry_inr, SSet.yonedaEquiv_symm_comp]
  have h := pinchedHomCurry_postcomp (pinchedHomUncurry f)
    (pinchedHomUncurry_inl f) (pinchedHomUncurry_inr f) p hx hy
  rw [pinchedHomCurry_uncurry] at h
  have h' := congrArg pinchedHomUncurry h
  rw [pinchedHomUncurry_curry] at h'
  exact h'

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors
