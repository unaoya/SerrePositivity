module


public meta import SerrePositivity.Util.Citation
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.MappingSpaceMap
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.VertexFiber
public import SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.RelativeOuterHornOp

/-!
概要：inner fibration が右 pinched 写像空間上に誘導する右ファイブレーション。
方針：正の添字のホーンに定値の最終面を加え、元の射の内ホーンを持ち上げる。
規約：始域・終域の quasicategory 性はこの持ち上げには不要。
使われ方：HTT §2.2、Kerodon Proposition 4.8.4.5（Tag 05AR） の写像空間への還元。

対応節は Kerodon 4.6（Tag 01J3）。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
universe u
open CategoryTheory SSet
open scoped Simplicial
namespace SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-- 概要：右 pinched 写像空間の射は正の添字の全ホーンを相対的に充填できる。
方針：一つ高い次元の内ホーンを作り、射 p に沿って指定単体へ持ち上げる。
規約：零番目の外側ホーンは含めない。
使われ方：HTT §2.2、Kerodon §4.8.4（Tag 06SQ） の相対的な写像空間。 -/
lemma pinchedHomMap_rightHornFilling {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p]
    (x y : X _⦋0⦌)
    (n : ℕ) (i : Fin (n + 2)) (hi : 0 < i)
    (f : ∀ (j : Fin (n + 2)) (_ : j ≠ i), (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y)
    (hf : horn.IsCompatible f)
    (b : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
      (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y))
    (hb : ∀ (j : Fin (n + 2)) (hj : j ≠ i),
      f j hj ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y = stdSimplex.δ j ≫ b) :
    ∃ F : (Δ[n + 1] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y,
      (∀ (j : Fin (n + 2)) (hj : j ≠ i), stdSimplex.δ j ≫ F = f j hj) ∧
      F ≫ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y = b := by
  let fs : ∀ (j : Fin (n + 3)) (_ : j ≠ i.castSucc), (Δ[n + 1] : SSet.{u}) ⟶ X :=
    fun j ↦ Fin.lastCases (fun _ ↦ SSet.const x)
      (fun j hj ↦ SSet.yonedaEquiv.symm
        (SSet.yonedaEquiv (f j (fun h ↦ hj (congrArg Fin.castSucc h)))).val) j
  have hfs : horn.IsCompatible fs := by
    intro j k hj hk hjk
    induction k using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact False.elim ((lt_irrefl _) hjk)
      | cast j =>
        apply SSet.yonedaEquiv.injective
        have hpred : (Fin.last (n + 2)).pred (Fin.ne_zero_of_lt hjk) = Fin.last (n + 1) := rfl
        have hcast : j.castSucc.castPred (Fin.ne_last_of_lt hjk) = j := rfl
        rw [hpred, hcast]
        dsimp only [fs]
        rw [Fin.lastCases_castSucc, Fin.lastCases_last,
          stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply,
          SSet.comp_const]
        change X.δ (Fin.last (n + 1))
          (SSet.yonedaEquiv (f j (fun h ↦ hj (congrArg Fin.castSucc h)))).val =
            _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x n
        have hs := (SSet.yonedaEquiv (f j
          (fun h ↦ hj (congrArg Fin.castSucc h)))).source
        rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front_eq_δ] at hs
        exact hs
    | cast k =>
      induction j using Fin.lastCases with
      | last => exact False.elim ((not_lt_of_ge (Fin.le_last _)) hjk)
      | cast j =>
        have hj' : j ≠ i := fun h ↦ hj (congrArg Fin.castSucc h)
        have hk' : k ≠ i := fun h ↦ hk (congrArg Fin.castSucc h)
        have hjk' : j < k := hjk
        cases n with
        | zero =>
          fin_cases i <;> fin_cases j <;> fin_cases k <;> first
            | exact (hj' rfl).elim
            | exact (hk' rfl).elim
            | exact False.elim ((show ¬ _ from by decide) hjk')
        | succ n =>
          have h := congrArg (fun F : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y ↦
            (SSet.yonedaEquiv F).val) (hf.δ_pred_comp j k hj' hk' hjk')
          simp only [stdSimplex.yonedaEquiv_δ_comp] at h
          change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (k.pred (Fin.ne_zero_of_lt hjk')))).op
              (SSet.yonedaEquiv (f j hj')).val =
            X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ (j.castPred (Fin.ne_last_of_lt hjk')))).op
              (SSet.yonedaEquiv (f k hk')).val at h
          rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedExtend_δ, _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedExtend_δ] at h
          apply SSet.yonedaEquiv.injective
          have hpred : k.castSucc.pred (Fin.ne_zero_of_lt hjk) =
              (k.pred (Fin.ne_zero_of_lt hjk')).castSucc := by apply Fin.ext; rfl
          have hcast : j.castSucc.castPred (Fin.ne_last_of_lt hjk) =
              (j.castPred (Fin.ne_last_of_lt hjk')).castSucc := by apply Fin.ext; rfl
          rw [hpred, hcast]
          dsimp only [fs]
          rw [Fin.lastCases_castSucc, Fin.lastCases_castSucc,
            stdSimplex.yonedaEquiv_δ_comp, stdSimplex.yonedaEquiv_δ_comp,
            SSet.yonedaEquiv.apply_symm_apply, SSet.yonedaEquiv.apply_symm_apply]
          exact h
  obtain ⟨σ, hσ⟩ := hfs.exists_desc
  have hi₀ : (0 : Fin (n + 3)) < i.castSucc := hi
  have hi₁ : i.castSucc < Fin.last (n + 2) := Fin.castSucc_lt_last i
  let β := SSet.yonedaEquiv.symm (SSet.yonedaEquiv b).val
  have hw : σ ≫ p = (horn (n + 2) i.castSucc).ι ≫ β := by
    apply horn.hom_ext'
    intro j hj
    rw [← Category.assoc, hσ j hj, horn.ι_ι_assoc]
    induction j using Fin.lastCases with
    | last =>
      dsimp only [fs]
      rw [Fin.lastCases_last, SSet.const_comp]
      apply SSet.yonedaEquiv.injective
      rw [stdSimplex.yonedaEquiv_δ_comp]
      dsimp only [β]
      rw [SSet.yonedaEquiv.apply_symm_apply]
      change _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant (p.app (Opposite.op ⦋0⦌) x) (n + 1) =
        Y.δ (Fin.last (n + 2)) (SSet.yonedaEquiv b).val
      have h := (SSet.yonedaEquiv b).source
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front_eq_δ] at h
      exact h.symm
    | cast j =>
      have hj' : j ≠ i := fun h ↦ hj (congrArg Fin.castSucc h)
      dsimp only [fs]
      rw [Fin.lastCases_castSucc]
      apply SSet.yonedaEquiv.injective
      rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply,
        stdSimplex.yonedaEquiv_δ_comp]
      have h := congrArg (fun f : (Δ[n] : SSet.{u}) ⟶ _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
        (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y) ↦
          (SSet.yonedaEquiv f).val) (hb j hj')
      rw [SSet.yonedaEquiv_comp, stdSimplex.yonedaEquiv_δ_comp] at h
      change p.app (Opposite.op ⦋n + 1⦌) (SSet.yonedaEquiv (f j hj')).val =
        Y.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ j)).op (SSet.yonedaEquiv b).val at h
      rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedExtend_δ] at h
      dsimp only [β]
      rw [SSet.yonedaEquiv.apply_symm_apply]
      convert h using 1 <;> rfl
  have := InnerFibration.mem (q := p) (horn (n + 2) i.castSucc).ι
    (horn_ι_mem_innerHornInclusions hi₀ hi₁)
  let sq : CommSq σ (horn (n + 2) i.castSucc).ι p β := ⟨hw⟩
  let F := sq.lift
  have hF : σ = (horn (n + 2) i.castSucc).ι ≫ F := sq.fac_left.symm
  have hface (j : Fin (n + 3)) (hj : j ≠ i.castSucc) :
      stdSimplex.δ j ≫ F = fs j hj := by
    rw [← horn.ι_ι_assoc i.castSucc j hj, ← hF]
    exact hσ j hj
  have hFcast (j : Fin (n + 2)) (hj : j ≠ i) :
      stdSimplex.δ j.castSucc ≫ F = SSet.yonedaEquiv.symm
        (SSet.yonedaEquiv (f j hj)).val := by
    simpa only [fs, Fin.lastCases_castSucc] using
      hface j.castSucc (fun h ↦ hj (Fin.castSucc_injective _ h))
  have hFlast : stdSimplex.δ (Fin.last (n + 2)) ≫ F = SSet.const x := by
    simpa only [fs, Fin.lastCases_last] using
      hface (Fin.last (n + 2)) (Fin.castSucc_ne_last i).symm
  let s := SSet.yonedaEquiv F
  have hlast : X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front (n + 1)).op s = _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.constant x (n + 1) := by
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.front_eq_δ]
    change X.δ (Fin.last (n + 2)) (SSet.yonedaEquiv F) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, hFlast]
    rfl
  have htgt : X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex (n + 1)).op s = y := by
    have hzero : (0 : Fin (n + 2)) ≠ i := ne_of_lt hi
    have hfront : X.δ (0 : Fin (n + 3)) s =
        (SSet.yonedaEquiv (f 0 hzero)).val := by
      have h0 : stdSimplex.δ (0 : Fin (n + 3)) ≫ F =
          SSet.yonedaEquiv.symm (SSet.yonedaEquiv (f 0 hzero)).val := by
        simpa only [Fin.castSucc_zero] using hFcast 0 hzero
      rw [← stdSimplex.yonedaEquiv_δ_comp, h0]
      exact SSet.yonedaEquiv.apply_symm_apply _
    have hl := _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex_extend (SimplexCategory.δ (0 : Fin (n + 2)))
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedExtend_δ] at hl
    rw [← hl, op_comp, CategoryTheory.Functor.map_comp_apply]
    change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.lastVertex n).op (X.δ 0 s) = y
    rw [hfront]
    exact (SSet.yonedaEquiv (f 0 hzero)).target
  let t : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom x y) _⦋n + 1⦌ := ⟨s, hlast, htgt⟩
  refine ⟨SSet.yonedaEquiv.symm t, ?_, ?_⟩
  · intro j hj
    apply SSet.yonedaEquiv.injective
    rw [stdSimplex.yonedaEquiv_δ_comp, SSet.yonedaEquiv.apply_symm_apply]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    change X.map (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.extend (SimplexCategory.δ j)).op s =
      (SSet.yonedaEquiv (f j hj)).val
    rw [_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedExtend_δ]
    change X.δ j.castSucc (SSet.yonedaEquiv F) = _
    rw [← stdSimplex.yonedaEquiv_δ_comp, hFcast j hj]
    exact SSet.yonedaEquiv.apply_symm_apply _

  · apply SSet.yonedaEquiv.injective
    rw [SSet.yonedaEquiv_comp, SSet.yonedaEquiv.apply_symm_apply]
    apply _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.PinchedHom.Simplex.ext
    have h := congrArg SSet.yonedaEquiv sq.fac_right
    rw [SSet.yonedaEquiv_comp] at h
    change p.app (Opposite.op ⦋n + 2⦌) (SSet.yonedaEquiv F) = (SSet.yonedaEquiv b).val
    simpa only [β, SSet.yonedaEquiv.apply_symm_apply] using h

/-- 概要：inner fibration が右 pinched 写像空間上に誘導する射は右ファイブレーション。
方針：ホーンの面の相対充填をホーンの持ち上げ問題へまとめる。
規約：標的・始域の quasicategory 性は不要。
使われ方：HTT §2.2、Kerodon Proposition 4.8.4.5（Tag 05AR） の写像空間の fiber。 -/
instance pinchedHomMap_rightFibration {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p]
    (x y : X _⦋0⦌) : _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.LeftAndRightFibrations.RightFibration (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y) where
  mem := by
    intro A B j hj
    cases hj with
    | @intro n i hi =>
      constructor
      intro a b sq
      obtain ⟨F, hF, hFp⟩ := pinchedHomMap_rightHornFilling p x y n i hi
        (fun j hj ↦ horn.ι i j hj ≫ a) (horn.IsCompatible.of_hom a) b (by
          intro j hj
          rw [Category.assoc, sq.w, ← Category.assoc, horn.ι_ι])
      exact CommSq.HasLift.mk' { l := F, fac_left := horn.hom_ext' hF, fac_right := hFp }

/-- 概要：inner fibration による右写像空間の射の各頂点上の fiber は Kan 複体。
方針：右ファイブレーションの頂点上の fiber の Kan 性を適用する。
規約：元の単体集合の quasicategory 性は不要。
使われ方：Kerodon §4.8.4（Tag 06SQ） の充満忠実性から境界充填への移行。 -/
lemma pinchedHomMap_vertexFiber_kanComplex {X Y : SSet.{u}} (p : X ⟶ Y) [InnerFibration p]
    (x y : X _⦋0⦌) (s : (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.Basic.pinchedHom
      (p.app (Opposite.op ⦋0⦌) x) (p.app (Opposite.op ⦋0⦌) y)) _⦋0⦌) :
    KanComplex (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y) s) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.vertexFiber_kanComplex _ _

/-- 概要：quasicategory 間の inner fibration の右写像空間の射は全ホーンを持ち上げる。
方針：右写像空間の Kan 性と射の右ファイブレーション性を組み合わせる。
規約：全ホーンの lifting property を明示し、モデル構造を使わない。
使われ方：HTT §2.2、Kerodon §4.8.4（Tag 06SQ） の写像空間の相対充填。 -/
lemma pinchedHomMap_hasLiftingProperty_horn {X Y : SSet.{u}}
    [Quasicategory X] [Quasicategory Y] (p : X ⟶ Y) [InnerFibration p]
    (x y : X _⦋0⦌) (n : ℕ) (i : Fin (n + 2)) :
    HasLiftingProperty (horn (n + 1) i).ι (_root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.FullFaithfulAndEssentiallySurjectiveFunctors.pinchedHomMap p x y) :=
  _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.IsomorphismsAndIsofibrations.rightFibration_hasLiftingProperty_horn_of_kanComplex _ n i

end SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces

/-! Literature correspondences from the reviewed coverage tables. -/

/-! Reviewed literature correspondences. -/
attribute [cite HTT "2.4.4.1"] _root_.SerrePositivity.InfinityCategories.Kerodon.TheHomotopyTheoryOfInfinityCategories.MorphismSpaces.pinchedHomMap_hasLiftingProperty_horn
