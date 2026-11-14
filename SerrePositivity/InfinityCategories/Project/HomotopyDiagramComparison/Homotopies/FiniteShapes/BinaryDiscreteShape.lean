module

public import SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison.FunctorComparison.DiscreteNerveOpposite

/-!
概要：元の二点直和を、小さい離散二点 nerve と厳密に比較する。
方針：離散 nerve の各単体を同じ頂点の定値単体へ戻す。
規約：対象の二点と元の直和包含を保持。使われ方：有限積条件を二項対角へ渡す。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison

/-- 元の離散 nerve の単体は、その元の最初の対象の定値単体そのもの。 -/
lemma discreteNerveSimplex_eq_const {J : Type u} {n : ℕ}
    (s : (nerve (Discrete J)) _⦋n⦌) :
    s = (Functor.const (Fin (n + 1))).obj (s.obj 0) := by
  apply nerve.ext_of_isThin
  funext i
  have h : s.obj 0 = s.obj i := IsDiscrete.eq_of_hom
    (s.map (homOfLE (Fin.zero_le i)))
  exact h.symm

/-- 元の二点直和の第一包含。 -/
abbrev binaryDiscreteLeft :
    (Δ[0] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u}) := coprod.inl
/-- 元の二点直和の第二包含。 -/
abbrev binaryDiscreteRight :
    (Δ[0] : SSet.{u}) ⟶ (Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u}) := coprod.inr

/-- 離散二点の元のラベルを、元の二点直和の同じ側へ送る。 -/
def binaryDiscreteToCoproduct : nerve (Discrete (ULift.{u} Bool)) ⟶
    (Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u}) where
  app n := ↾fun s => if (s.obj 0).as.down then
    (binaryDiscreteRight.{u}).app n (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n.unop.len)
    else (binaryDiscreteLeft.{u}).app n
      (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n.unop.len)
  naturality {n m} α := by
    apply ConcreteCategory.hom_ext
    intro s
    have hv : (((nerve (Discrete (ULift.{u} Bool))).map α) s).obj 0 = s.obj 0 := by
      change s.obj _ = s.obj 0
      exact (IsDiscrete.eq_of_hom (s.map (homOfLE (Fin.zero_le _)))).symm
    change (if _ then _ else _) =
      ((Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u})).map α (if _ then _ else _)
    have hvb : ((((nerve (Discrete (ULift.{u} Bool))).map α).hom'.toFun s).obj 0).as.down =
        (s.obj 0).as.down := congrArg (fun x => x.as.down) hv
    rw [hvb]
    have hc : (Δ[0] : SSet.{u}).map α
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n.unop.len) =
        _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) m.unop.len := by
      apply SSet.stdSimplex.ext
      intro i
      apply Fin.ext
      omega
    cases (s.obj 0).as.down
    · simp only [Bool.false_eq_true, ↓reduceIte]
      simpa only [ConcreteCategory.comp_apply, hc] using
        (ConcreteCategory.congr_hom ((binaryDiscreteLeft.{u}).naturality α)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n.unop.len))
    · simp only [↓reduceIte]
      simpa only [ConcreteCategory.comp_apply, hc] using
        (ConcreteCategory.congr_hom ((binaryDiscreteRight.{u}).naturality α)
          (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n.unop.len))

/-- 元の二点直和の二つの頂点を、同じ離散二点へ送る。 -/
def coproductToBinaryDiscrete : (Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u}) ⟶
    nerve (Discrete (ULift.{u} Bool)) :=
  coprod.desc (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk (ULift.up false))))
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk (ULift.up true))))

/-- 第一ラベルの定値族を戻すと、元の第一包含そのもの。 -/
lemma binaryDiscreteToCoproduct_left :
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk (ULift.up false))) :
      (Δ[0] : SSet.{u}) ⟶ nerve (Discrete (ULift.{u} Bool))) ≫
      binaryDiscreteToCoproduct = binaryDiscreteLeft := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change binaryDiscreteLeft.app n
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n.unop.len) = binaryDiscreteLeft.app n s
  apply congrArg (binaryDiscreteLeft.app n)
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  omega

/-- 第二ラベルの定値族を戻すと、元の第二包含そのもの。 -/
lemma binaryDiscreteToCoproduct_right :
    (SSet.const (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.TheSliceAndJoinConstructions.nerveVertex (Discrete.mk (ULift.up true))) :
      (Δ[0] : SSet.{u}) ⟶ nerve (Discrete (ULift.{u} Bool))) ≫
      binaryDiscreteToCoproduct = binaryDiscreteRight := by
  apply SSet.hom_ext
  intro n
  apply ConcreteCategory.hom_ext
  intro s
  change binaryDiscreteRight.app n
    (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n.unop.len) = binaryDiscreteRight.app n s
  apply congrArg (binaryDiscreteRight.app n)
  apply SSet.stdSimplex.ext
  intro i
  apply Fin.ext
  omega

/-- 元の二点直和と離散二点 nerve の、元の二点を保つ厳密な同型。 -/
def binaryDiscreteNerveIso : (Δ[0] : SSet.{u}) ⨿ (Δ[0] : SSet.{u}) ≅
    nerve (Discrete (ULift.{u} Bool)) where
  hom := coproductToBinaryDiscrete
  inv := binaryDiscreteToCoproduct
  hom_inv_id := by
    apply coprod.hom_ext
    · rw [← Category.assoc, coproductToBinaryDiscrete, coprod.inl_desc]
      exact binaryDiscreteToCoproduct_left
    · rw [← Category.assoc, coproductToBinaryDiscrete, coprod.inr_desc]
      exact binaryDiscreteToCoproduct_right
  inv_hom_id := by
    apply SSet.hom_ext
    rintro ⟨⟨n⟩⟩
    apply ConcreteCategory.hom_ext
    intro s
    cases h : (s.obj 0).as.down
    · have ho : s.obj 0 = Discrete.mk (ULift.up false) := Discrete.ext (ULift.ext h)
      have hs := discreteNerveSimplex_eq_const s
      rw [ho] at hs
      rw [hs]
      change ((binaryDiscreteLeft ≫ coproductToBinaryDiscrete).app (Opposite.op ⦋n⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n)) = _
      rw [coproductToBinaryDiscrete, coprod.inl_desc]
      rfl
    · have ho : s.obj 0 = Discrete.mk (ULift.up true) := Discrete.ext (ULift.ext h)
      have hs := discreteNerveSimplex_eq_const s
      rw [ho] at hs
      rw [hs]
      change ((binaryDiscreteRight ≫ coproductToBinaryDiscrete).app (Opposite.op ⦋n⦌)
        (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (stdSimplex.obj₀Equiv.symm 0) n)) = _
      rw [coproductToBinaryDiscrete, coprod.inr_desc]
      rfl

end SerrePositivity.InfinityCategories.Project.HomotopyDiagramComparison
