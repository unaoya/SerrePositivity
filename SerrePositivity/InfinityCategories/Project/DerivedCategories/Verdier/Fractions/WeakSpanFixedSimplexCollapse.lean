module

public meta import SerrePositivity.InfinityCategories.Project.SimplicialCombinatorics.DeprecatedAlias
public import SerrePositivity.KST.Fibration.WeakSpanKanQuotientFamily
public import SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.OrdinaryComparisonPrism

/-!
概要：元の両端固定 span の全単体に対する、底の定値単体への同時収縮。
方針：固定した第二終点への射影を計算し、零単体からの退化作用素を自然変換にする。
規約：元の固定 span と全単体を保持する。一般の局所化・商 API は追加しない。
使われ方：元の実全族写像の fiber と、同じ単体圏上の実単位の比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory SSet
open scoped _root_.Simplicial
open SerrePositivity.InfinityCategories
open SerrePositivity.KST.LocalizingInvariants
namespace SerrePositivity.KST.Fibration
end SerrePositivity.KST.Fibration
namespace SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions
open _root_.SerrePositivity.KST.Fibration
variable {A B : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.StableCategory.{u}} (i : _root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.ExactMap A B) (x y : B.obj _⦋0⦌)

/-- 概要：元の両端固定 span の全族射影は同じ第二終点の定値射。
方針：元の全族包含と、元の固定境界の第二終点計算を使う。
規約：全単体上の実写像の等式。
使われ方：固定 span の単体全族を同じ底 fiber 内で比較する。 -/
theorem weakSpanFixedFamily_projection :
    fixedMarkedSpanToFamily B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y ≫
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x = SSet.const y := by
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection, ← Category.assoc,
    fixedMarkedSpanToFamily_inclusion, fixedMarkedSpan_target]

/-- 概要：固定 span の全単体の底像へ、元の第二終点の零単体から同時に退化する。
方針：各単体の次数から零次への唯一の作用素を使い、その自然性を保持する。
規約：各単体の底像は元の実射影による像。別の定値図式へ置換しない。
使われ方：元の全族の初頂点降下と固定 fiber 単位との比較 prism。 -/
def weakSpanFixedSimplexCollapse :
    (Functor.const (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory
      (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y))).obj
      (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) y) ⟶
    _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (fixedMarkedSpanToFamily B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y) ⋙
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x) where
  app t := ⟨{ hom := (SimplexCategory.const t.objDown.obj.unop ⦋0⦌ 0).op
              map_val := by
                have h := congrArg (fun f => f.app t.objDown.obj t.objDown.val)
                  (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedFamily_projection i x y)
                exact h.symm }⟩
  naturality {s t} f := by
    apply ULift.ext
    apply CategoryTheory.Functor.Elements.Hom.ext
    apply Quiver.Hom.unop_inj
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext k
    change (_ : Fin 1) = _
    exact Subsingleton.elim _ _


/-- 概要：同じ固定 span の退化比較 prism は元の底で全パラメータに定値。
方針：prism の各単体の初対象を計算し、その全退化単体を初頂点作用素で読む。
規約：辺のホモトピー類だけでなく、全 prism の実写像を固定する。
使われ方：元の全族射影の引き戻しへの同じ prism の持ち上げ。 -/
theorem weakSpanFixedSimplexCollapse_base :
    _root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.ordinaryComparisonPrism (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedSimplexCollapse i x y) ≫
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj = SSet.const y := by
  let H := Functor.uncurry.obj (ComposableArrows.mk₁ (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedSimplexCollapse i x y))
  have hv (d : Fin 2)
      (t : _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)) :
      (H.obj (d, t)).objDown.val =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y (H.obj (d, t)).objDown.obj.unop.len := by
    fin_cases d
    · exact (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedConstant_zero y).symm
    · exact congrArg (fun f => f.app t.objDown.obj t.objDown.val)
        (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedFamily_projection i x y)
  apply SSet.hom_ext
  rintro ⟨⟨n⟩⟩
  apply ConcreteCategory.hom_ext
  intro s
  change nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory
    (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)) _⦋n⦌ × (Δ[1] : SSet.{u}) _⦋n⦌ at s
  let τ := (s.2.down.toOrderHom.monotone.functor.prod' s.1) ⋙ H
  let α := _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMorphism τ
  let β := SimplexCategory.const (τ.obj 0).objDown.obj.unop ⦋0⦌ 0
  have ht := hv (s.2.down.toOrderHom 0) (s.1.obj 0)
  have hc : α ≫ β = SimplexCategory.const ⦋n⦌ ⦋0⦌ 0 := Subsingleton.elim _ _
  change B.obj.map α.op (τ.obj 0).objDown.val = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant y n
  calc
    _ = B.obj.map α.op (B.obj.map β.op y) := congrArg (B.obj.map α.op) ht
    _ = B.obj.map (β.op ≫ α.op) y := (B.obj.map_comp_apply β.op α.op y).symm
    _ = _ := by rw [← op_comp, hc]; rfl


/-- 概要：元の固定 span 全族を、同じ第二終点の零単体上の引き戻しへ入れる。
方針：元の全族包含と指定零単体の定値射を同じ引き戻しに束ねる。
規約：span の座標と底の零単体を保持する。
使われ方：同じ実単位の固定 fiber 制限。 -/
def weakSpanFixedZeroSimplexLift :
    fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y ⟶
      pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj) :=
  pullback.lift (fixedMarkedSpanToFamily B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexIndex (n := ⦋0⦌) y))) (by
      rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedFamily_projection, SSet.const_comp,
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.transportSimplexFirstVertexMap_zeroIndex])

/-- 概要：元の固定 span の全単体を零単体上の同じ全族へ比較する実 prism。
方針：span 座標を全時刻固定し、底の全退化比較を引き戻しへ持ち上げる。
規約：元の全族への射影を全パラメータで厳密に固定する。
使われ方：相対初頂点降下後の同じ実全族写像の fiber 制限を比較する。 -/
def weakSpanFixedSimplexFamilyPrism :
    nerve (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.TransportSimplexCategory (fixedMarkedSpans B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)) ⊗
      Δ[1] ⟶ pullback (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj) :=
  pullback.lift
    (fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap _ ≫
      fixedMarkedSpanToFamily B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)
    (_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.ordinaryComparisonPrism (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedSimplexCollapse i x y)) (by
      rw [Category.assoc, Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedFamily_projection,
        SSet.comp_const, SSet.comp_const, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedSimplexCollapse_base])

/-- 概要：同じ比較 prism の元の span 座標は全時刻固定。
方針：元の引き戻しの第一射影を計算する。
規約：元の全単体上の実写像の等式。
使われ方：全族の比較が同じ span の上にあることの確認。 -/
theorem weakSpanFixedSimplexFamilyPrism_family :
    _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedSimplexFamilyPrism i x y ≫
      pullback.fst (_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.markedSpanFamilyProjection B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap B.obj) =
      fst _ _ ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap _ ≫
        fixedMarkedSpanToFamily B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y := by
  exact pullback.lift_fst _ _ _


/-- 概要：同じ実 prism の始端は、零単体上の元の固定 span 全族そのもの。
方針：両引き戻し射影で始端を計算する。
規約：全単体上の厳密な等式。
使われ方：元の単体圏単位の固定 fiber 制限を回収する。 -/
theorem weakSpanFixedSimplexFamilyPrism_zero :
    SSet.ι₀ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedSimplexFamilyPrism i x y =
      _root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap _ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedZeroSimplexLift i x y := by
  apply pullback.hom_ext
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedSimplexFamilyPrism,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedZeroSimplexLift, pullback.lift_fst]
    rw [← Category.assoc, SSet.ι₀_fst, Category.id_comp]
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedSimplexFamilyPrism,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedZeroSimplexLift, pullback.lift_snd]
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.ordinaryComparisonPrism_zero, SSet.comp_const]
    rfl

/-- 概要：同じ実 prism の終端は、元の固定 span を全族の単体圏から持ち上げた射。
方針：第一射影に初頂点自然性、第二射影に元の単体関手の合成を使う。
規約：元の marked span 全族の全単体を保持する。
使われ方：相対降下が回収する指定制限と同じ実単位を照合する。 -/
theorem weakSpanFixedSimplexFamilyPrism_one :
    SSet.ι₁ ≫ _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedSimplexFamilyPrism i x y =
      nerveMap (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFunctor (fixedMarkedSpanToFamily B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)) ≫
        _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanTotalSimplexLift (i := i) x := by
  apply pullback.hom_ext
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedSimplexFamilyPrism,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanTotalSimplexLift, pullback.lift_fst]
    rw [← Category.assoc, SSet.ι₁_fst, Category.id_comp]
    exact (_root_.SerrePositivity.InfinityCategories.Kerodon.FibrationsOfInfinityCategories.CartesianFibrations.transportSimplexFirstVertexMap_naturality
      (fixedMarkedSpanToFamily B.obj (_root_.SerrePositivity.InfinityCategories.HA.StableInfinityCategories.Verdier.Fractions.weakEquivalences i) x y)).symm
  · simp only [Category.assoc, _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanFixedSimplexFamilyPrism,
      _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions.weakSpanKanTotalSimplexLift, pullback.lift_snd]
    rw [_root_.SerrePositivity.InfinityCategories.Project.FibrationAuxiliaries.FunctorCategories.ordinaryComparisonPrism_one]
    rfl

end SerrePositivity.InfinityCategories.Project.DerivedCategories.Verdier.Fractions

/-! F-2 compatibility names. Retain until the first stage-G checkpoint (IF-F §5). -/
public section
