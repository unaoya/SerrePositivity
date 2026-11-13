module
public import SerrePositivity.KST.SConstruction.DGOdotMilnorSourceKernelEquivalence
public import SerrePositivity.InfinityCategories.Project.DerivedCategories.MappingAndStability.Triangles.DGStableHomotopyEquivalence

/-!
概要：元対角始域を cell 増大屋根の終端として回収する指定 ν 同値を構成する。
方針：同じ厳密核比較の native 同値から dg 準同値を回収し、実 Perf 延長を適用する。
規約：元入力への増大と核比較の二辺を固定し、S 内の逆関手を仮定しない。
使われ方：17:53 採用の d④ の始域回収。
-/
@[expose] public section
noncomputable section
universe u
namespace SerrePositivity.KST.SConstruction
open CategoryTheory SSet DifferentialGraded InfinityCategories LocalizingInvariants
open scoped Simplicial
variable (R : Type u) [CommRing R] (d : DGOdotInput R)
local notation "A" => DGSmallPerfectBase R (_root_.SerrePositivity.InfinityCategories.HA.Section7_1_1.dgAlgebraCategory R (DGOdotInput.source d))
local notation "T" => DGCategoryCellResolution.Source R (A)
local notation "P" => dgQuotientImage R
  (DGLaxQuotientEndInput.diagonal (dgOdotQuotientInput R d))
local notation "K" => _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.resolvedDGQuotientThickFlatKernel R (DGOdotGluing R d) (P)
local notation "F" => dgOdotMilnorSourceKernelDGMap R d

/-- 概要：Milnor 条件から同じ厳密核比較は dg 準同値。
方針：実 native 本質的全射性を D の同じ H⁰ 比較で戻す。
規約：全 Hom 準同型性は元対角の判定から得る。使われ方：実 Perf 延長の同値性。 -/
theorem dgOdotMilnorSourceKernelDGMap_quasiEquivalence (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    QuasiEquivalence (F) := by
  refine ⟨dgOdotMilnorSourceKernelDGMap_homQuasiIso R d h, ⟨?_⟩⟩
  intro Y
  let y : K := ForgetEnrichment.to (Complex R) Y.as
  obtain ⟨x, ⟨v⟩⟩ := dgOdotMilnorSourceKernelNerve_essentiallySurjective R d h
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y)
  obtain ⟨x, rfl⟩ := _root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertexEquiv.symm.surjective x
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.VertexIso ((_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Functor.map (F)).app _ (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex x))
    (_root_.SerrePositivity.InfinityCategories.Kerodon.ExamplesOfInfinityCategories.DifferentialGradedCategories.Simplex.vertex y) at v
  rw [_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgFunctorNerve_vertex] at v
  exact ⟨(toHomotopy R (T)).obj (ForgetEnrichment.of (Complex R) x),
    ⟨_root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.dgH0IsoOfVertexIso R (K) v⟩⟩

/-- 概要：元対角始域への同じ増大の ν 像は同値。
方針：実準同値の一回 Perf 延長と宇宙持ち上げの保存を使用する。
規約：順方向は同じ元の S 辺。使われ方：元入力への屋根の脚。 -/
lemma dgOdotMilnorSourceAugmentationNu_isQCatEquivalence :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgOdotMilnorSourceAugmentationExactMap R d).hom := by
  let Aug := DGCategoryCellResolution.augmentation R (A)
  letI : (quasiEquivalencePerfectExtension R (T) (A) Aug).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence R _ _ Aug
      (DGCategoryCellResolution.augmentation_quasiEquivalence R (A))).isEquivalence_functor
  letI : (quasiEquivalencePerfectExtension R (dgOdotMilnorSourceCellInput R d)
      (dgOdotDiagonalSourceInput R d)
      (dgOdotMilnorSourceAugmentationInputMap R d).down).IsEquivalence :=
    dgKUniverseLiftFunctor_isMorita R (T) (A) Aug
  unfold dgOdotMilnorSourceAugmentationExactMap
  rw [dgKInputNuMap_eq]
  exact presentedPerfectDGMoritaAction_isQCatEquivalence R _ _
    (dgOdotMilnorSourceAugmentationInputMap R d).down

/-- 概要：同じ thick 平坦核への厳密比較の ν 像は Milnor 条件で同値。
方針：構成した dg 準同値の同じ実 Perf 延長を使う。
規約：追加の生成・完備化仮定なし。使われ方：始域回収屋根のもう一つの脚。 -/
lemma dgOdotMilnorSourceKernelNu_isQCatEquivalence (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) :
    _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.IsQCatEquivalence (dgOdotMilnorSourceKernelExactMap R d).hom := by
  letI : (quasiEquivalencePerfectExtension R (T) (K) (F)).IsEquivalence :=
    (quasiEquivalencePerfectEquivalence R _ _ (F)
      (dgOdotMilnorSourceKernelDGMap_quasiEquivalence R d h)).isEquivalence_functor
  letI : (quasiEquivalencePerfectExtension R (dgOdotMilnorSourceCellInput R d)
      (dgOdotMilnorFlatKernelInput R d)
      (dgOdotMilnorSourceKernelInputMap R d).down).IsEquivalence :=
    dgKUniverseLiftFunctor_isMorita R (T) (K) (F)
  unfold dgOdotMilnorSourceKernelExactMap
  rw [dgKInputNuMap_eq]
  exact presentedPerfectDGMoritaAction_isQCatEquivalence R _ _
    (dgOdotMilnorSourceKernelInputMap R d).down

/-- 概要：同じ元始域増大の順方向を持つ指定 ν 同値。
方針：構成済みの実同値証拠を束ねる。規約：元の S 辺の像を保持する。
使われ方：始域回収の終端。 -/
def dgOdotMilnorSourceAugmentationNuEquivalence : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorSourceCellInput R d)).obj
    (dgKInputStableValue R (dgOdotDiagonalSourceInput R d)).obj :=
  (dgOdotMilnorSourceAugmentationNu_isQCatEquivalence R d).choose

/-- 概要：同じ核比較の順方向を持つ指定 ν 同値。
方針：Milnor 条件からの実同値証拠を束ねる。規約：核比較を選び直さない。
使われ方：始域回収の共通始域側。 -/
def dgOdotMilnorSourceKernelNuEquivalence (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorSourceCellInput R d)).obj
    (dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)).obj :=
  (dgOdotMilnorSourceKernelNu_isQCatEquivalence R d h).choose

/-- 概要：同じ平坦核の ν 値から元対角始域値を回収する指定同値。
方針：厳密核比較の逆と元入力への実増大を合成する。
規約：逆は ν の下だけで使用する。使われ方：d④ の元始域回収。 -/
def dgOdotMilnorSourceRecoveryNuEquivalence (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.QCatEquivalence
    (dgKInputStableValue R (dgOdotMilnorFlatKernelInput R d)).obj
    (dgKInputStableValue R (dgOdotDiagonalSourceInput R d)).obj :=
  (dgOdotMilnorSourceKernelNuEquivalence R d h).symm.trans
    (dgOdotMilnorSourceAugmentationNuEquivalence R d)

/-- 概要：指定した始域回収は同じ cell 始域上で元入力への増大を回収する。
方針：同じ核比較同値の単位二胞体を増大で後合成する。
規約：全関手同型を保持する。使われ方：Sp の始域屋根の指定比較。 -/
def dgOdotMilnorSourceRecoveryNuRoof (h : _root_.SerrePositivity.InfinityCategories.Project.DerivedCategories.Gluing.DGGluingMilnorSquare R d) : _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorSourceKernelExactMap R d).hom ≫
      (dgOdotMilnorSourceRecoveryNuEquivalence R d h).hom)
    (dgOdotMilnorSourceAugmentationExactMap R d).hom := by
  change _root_.SerrePositivity.InfinityCategories.Kerodon.KanComplexes.TheHomotopyTheoryOfKanComplexes.FunctorIso
    ((dgOdotMilnorSourceKernelNuEquivalence R d h).hom ≫
      ((dgOdotMilnorSourceKernelNuEquivalence R d h).inv ≫
        (dgOdotMilnorSourceAugmentationNuEquivalence R d).hom))
    (dgOdotMilnorSourceAugmentationNuEquivalence R d).hom
  rw [← Category.assoc]
  simpa only [Category.id_comp] using
    ((dgOdotMilnorSourceKernelNuEquivalence R d h).homInvIso.postcomp
      (dgOdotMilnorSourceAugmentationNuEquivalence R d).hom)

end SerrePositivity.KST.SConstruction
