module

public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.NerveCone

/-!
概要：圏の反対と単体集合の順序反転の間の同型、および終対象の頂点包含の anodyne 性。
方針：合成可能な射列を逆転し、始対象の既存の anodyne 定理を反転関手で移す。
規約：圏とその Hom は同じ宇宙。圏の反対と単体集合の反転を同一視せず同型を構成する。
使われ方：Kerodon 4.7.3.22（Tag 02J5） とその双対、7.5.3.12 の重みの終対象による比較。

対応節は Kerodon 4.7（Tag 05EA）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
variable {C : Type u} [SmallCategory C]

private lemma chainMap_heq {n : ℕ} (F : ComposableArrows C n)
    {i j i' j' : Fin (n + 1)} (hi : i = i') (hj : j = j')
    (f : i ⟶ j) (g : i' ⟶ j') : HEq (F.map f) (F.map g) := by
  subst i'
  subst j'
  have h : f = g := Subsingleton.elim _ _
  subst g
  rfl
private lemma chainMapOp_heq {n : ℕ} (F : ComposableArrows C n)
    {i j i' j' : Fin (n + 1)} (hi : i = i') (hj : j = j')
    (f : i ⟶ j) (g : i' ⟶ j') : HEq (F.map f).op (F.map g).op := by
  subst i'
  subst j'
  have h : f = g := Subsingleton.elim _ _
  subst g
  rfl
/-- 概要：合成可能な射列の順序と射を反転して反対圏の射列にする。
方針：頂点 i は元の i.rev、射は元の逆向きの区間の射の op を取る。
規約：長さ n は保存する。
使われ方：Kerodon 4.7.3（Tag 02H6） の終対象側への双対化。 -/
def nerveReverseChain {n : ℕ} (F : ComposableArrows C n) : ComposableArrows Cᵒᵖ n where
  obj i := Opposite.op (F.obj i.rev)
  map {i j} h := (F.map (homOfLE (by simpa only [Fin.rev_le_rev] using leOfHom h))).op
  map_id i := by simp
  map_comp f g := by
    rw [← op_comp, ← F.map_comp]
    rfl
def nerveUnreverseChain {n : ℕ} (F : ComposableArrows Cᵒᵖ n) : ComposableArrows C n where
  obj i := (F.obj i.rev).unop
  map {i j} h := (F.map (homOfLE (by simpa only [Fin.rev_le_rev] using leOfHom h))).unop
  map_id i := by simp
  map_comp f g := by
    rw [← unop_comp, ← F.map_comp]
    rfl
/-- 概要：射列を反転して逆反転すると元に戻る。
方針：Fin.rev の二重適用と順序圏の射の一意性を使う。
規約：関手としての厳密な等式。
使われ方：Kerodon 4.7.3（Tag 02H6） の反転同型の単射性。 -/
lemma nerveUnreverse_reverse {n : ℕ} (F : ComposableArrows C n) :
    nerveUnreverseChain (nerveReverseChain F) = F := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro i
    exact congrArg F.obj (Fin.rev_rev i)
  · intro i j h
    exact chainMap_heq F (Fin.rev_rev i) (Fin.rev_rev j) _ h
/-- 概要：反対圏の射列を逆反転して反転すると元に戻る。
方針：頂点の二重反転と射の op と unop の相殺を使う。
規約：関手としての厳密な等式。
使われ方：Kerodon 4.7.3（Tag 02H6） の反転同型の全射性。 -/
lemma nerveReverse_unreverse {n : ℕ} (F : ComposableArrows Cᵒᵖ n) :
    nerveReverseChain (nerveUnreverseChain F) = F := by
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro i
    exact congrArg F.obj (Fin.rev_rev i)
  · intro i j h
    exact chainMap_heq F (Fin.rev_rev i) (Fin.rev_rev j) _ h
/-- 概要：N(C) の単体の順序反転から N(Cᵒᵖ) への自然な射。
方針：各単体の射列を逆転し、添字の反転と前合成の可換性を示す。
規約：面と退化の全てに可換。
使われ方：Kerodon 4.7.3（Tag 02H6） の頂点包含の双対化。 -/
def nerveOppositeMap : (nerve C).op ⟶ nerve Cᵒᵖ where
  app _ := ↾fun F => nerveReverseChain F
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro F
    refine CategoryTheory.Functor.hext ?_ ?_
    · intro i
      change Opposite.op (F.obj ((α.unop.toOrderHom i.rev.rev).rev)) =
        Opposite.op (F.obj ((α.unop.toOrderHom i).rev))
      simp only [Fin.rev_rev]
    · intro i j h
      exact chainMapOp_heq F
        (congrArg (fun k => (α.unop.toOrderHom k).rev) (Fin.rev_rev j))
        (congrArg (fun k => (α.unop.toOrderHom k).rev) (Fin.rev_rev i)) _ _
/-- 概要：単体の順序を反転した nerve と反対圏の nerve の同型。
方針：逆反転による成分ごとの全単射から同型性を得る。
規約：同型の順射は nerveOppositeMap そのもの。
使われ方：Kerodon 4.7.3（Tag 02H6） とその双対の持ち上げ問題の移送。 -/
noncomputable def nerveOppositeIso : (nerve C).op ≅ nerve Cᵒᵖ := by
  have : IsIso (nerveOppositeMap (C := C)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro n
    rw [isIso_iff_bijective]
    constructor
    · intro F G h
      have h' := congrArg nerveUnreverseChain h
      change nerveUnreverseChain (nerveReverseChain F) =
        nerveUnreverseChain (nerveReverseChain G) at h'
      simpa only [nerveUnreverse_reverse] using h'
    · intro F
      exact ⟨nerveUnreverseChain F, nerveReverse_unreverse F⟩
  exact asIso nerveOppositeMap
/-- 概要：nerve の反転同型は対象の頂点包含を反対圏の同じ対象の頂点包含へ移す。
方針：全次数で定値の射列の反転を計算する。
規約：Δ[0] の反転も標準の同型で明示する。
使われ方：Kerodon 4.7.3.22（Tag 02J5） の終対象側の頂点の arrow 同型。 -/
lemma nerveOppositeMap_point (c : C) :
    SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c) ≫ nerveOppositeMap =
      (stdSimplex.opIso ⦋0⦌).hom ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (Opposite.op c) := by
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro i
    rfl
  · intro i j h
    rfl
/-- 概要：反転後に left anodyne な射は元では right anodyne。
方針：右 fibration の反転が左 fibration であることと反転関手の圏同値を使う。
規約：始域・終域の quasicategory 性は不要。
使われ方：Kerodon 4.3.7（Tag 018P） の双対な anodyne 性の移送。 -/
lemma rightAnodyne_of_op_left {A B : SSet.{u}} (f : A ⟶ B)
    (hf : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions (SSet.opFunctor.map f)) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions f := by
  intro E D p hp
  have : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration p := ⟨hp⟩
  have : SSet.opFunctor.{u}.IsEquivalence := SSet.opEquivalence.isEquivalence_functor
  exact (SSet.opFunctor.hasLiftingProperty_iff_of_isEquivalence f p).mp
    (hf (SSet.opFunctor.map p) _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.LeftFibration.mem)
/-- 概要：圏の終対象の頂点の nerve への包含は right anodyne。
方針：反対圏の始対象の頂点の left anodyne 性を二つの反転同型で移す。
規約：圏の対象と Hom は同じ宇宙。
使われ方：Kerodon 4.7.3.22（Tag 02J5）、7.5.3.12（Tag 03B1） の終対象を持つ重みの比較。 -/
lemma nervePoint_terminal_rightAnodyne {c : C} (hc : CategoryTheory.Limits.IsTerminal c) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.rightAnodyneExtensions (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c) := by
  apply rightAnodyne_of_op_left
  let e : Arrow.mk (SSet.opFunctor.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint c)) ≅
      Arrow.mk (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint (Opposite.op c)) :=
    Arrow.isoMk (stdSimplex.opIso ⦋0⦌) nerveOppositeIso (nerveOppositeMap_point c)
  exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.leftAnodyneExtensions.arrow_mk_iso_iff e).2 (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nervePoint_leftAnodyne (hc.op C))

/-- 概要：nerve の反転同型は通常の関手に自然。
方針：射列への関手の後合成と射列の反転を各頂点と射で比較する。
規約：反対関手 F.op と単体集合の反転 SSet.opFunctor を区別する。
使われ方：Kerodon 4.7.3（Tag 02H6）、7.5.3.12（Tag 03B1） の重みの包含の双対化。 -/
lemma nerveOppositeMap_naturality {D : Type u} [SmallCategory D] (F : C ⥤ D) :
    SSet.opFunctor.map (nerveMap F) ≫ nerveOppositeMap =
      nerveOppositeMap ≫ nerveMap F.op := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  refine CategoryTheory.Functor.hext ?_ ?_
  · intro i
    rfl
  · intro i j h
    rfl

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TruncatedObjectsAndHigherHomotopyCategories
