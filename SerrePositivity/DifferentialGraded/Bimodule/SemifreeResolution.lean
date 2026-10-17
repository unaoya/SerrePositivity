module
public import SerrePositivity.DifferentialGraded.Bimodule.RightModuleComparison
public import SerrePositivity.DifferentialGraded.Module.Semifree.Resolution

/-! # 任意bimoduleの積dg圏上のsemifree解像度

## 概要
任意bimoduleの積dg圏上のsemifree解像度。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanの依存。直接の利用箇所：Derived/BimoduleSemifreeComparison.lean、Tensor/
BimoduleRestrictionKFlat.lean。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w
namespace SerrePositivity.DifferentialGraded
open CategoryTheory Opposite
variable (A : Type u) [CommRing A] (B : Type v) (C : Type w)
  [DGCategory A B] [DGCategory A C] [Small.{u} B] [Small.{u} C]

/-- 積dg圏のopposite上の実際のfiltrationと主bimoduleへの準同型を保持する。
各右制限のsemifree性や相対K-flat性はこの定義には含めない。 -/
structure BimoduleSemifreeResolution (M : BimoduleCategory A B C) where
  source : ModuleCategory A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
  filtration : ModuleSemifreeFiltration A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ source
  π : (rightModuleBimoduleEquivalence A B C).functor.obj source ⟶ M
  quasiIso : BimoduleCategory.quasiIso A B C π

namespace BimoduleSemifreeResolution
variable {A B C} {M : BimoduleCategory A B C}

/-- 両作用に全Hom自然な主bimodule圏の対象としての解像度。 -/
def obj (P : BimoduleSemifreeResolution A B C M) : BimoduleCategory A B C :=
  (rightModuleBimoduleEquivalence A B C).functor.obj P.source

lemma semifree (P : BimoduleSemifreeResolution A B C M) :
    moduleSemifree A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ P.source :=
  ⟨P.filtration⟩

lemma value_quasiIso (P : BimoduleSemifreeResolution A B C M) (b : B) (c : C) :
    QuasiIso ((BimoduleCategory.valueEvaluation A B C b c).map P.π) :=
  P.quasiIso b c

end BimoduleSemifreeResolution

/-- 既存の可算cell解像度を圏同値で運ぶ。元のfiltrationの証拠を保持する。 -/
def bimoduleCanonicalSemifreeResolution (M : BimoduleCategory A B C) :
    BimoduleSemifreeResolution A B C M where
  source := moduleResolutionCandidate A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    ((rightModuleBimoduleEquivalence A B C).inverse.obj M)
  filtration := moduleResolutionSemifreeFiltration A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
    ((rightModuleBimoduleEquivalence A B C).inverse.obj M)
  π := (rightModuleBimoduleEquivalence A B C).functor.map
    (moduleResolutionCandidateπ A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ
      ((rightModuleBimoduleEquivalence A B C).inverse.obj M)) ≫
    ((rightModuleBimoduleEquivalence A B C).counitIso.app M).hom
  quasiIso := (BimoduleCategory.quasiIso A B C).comp_mem _ _
    ((rightModuleBimoduleEquivalence_quasiIso_iff A B C _).2
      (moduleResolutionCandidateπ_quasiIso A (DGTensorCategory A Bᵒᵖ C)ᵒᵖ _))
    ((BimoduleCategory.quasiIso A B C).of_isIso _)

theorem exists_semifree_bimodule_resolution (M : BimoduleCategory A B C) :
    Nonempty (BimoduleSemifreeResolution A B C M) :=
  ⟨bimoduleCanonicalSemifreeResolution A B C M⟩

end SerrePositivity.DifferentialGraded
