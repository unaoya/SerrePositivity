module
public import SerrePositivity.DifferentialGraded.Tensor.FunctorRestrictionQuasiIso
public import SerrePositivity.DifferentialGraded.Tensor.ChangeLeft
public import SerrePositivity.DifferentialGraded.Tensor.RestrictionComparisonCoherence
public import SerrePositivity.DifferentialGraded.Module.RestrictionCoherence

/-! # 制限後モデルを使うtensor比較の自己・推移整合性

## 概要
制限後モデルを使うtensor比較の自己・推移整合性。

## 方針
balanced tensor・全Hom自然性・作用の既存計算と普遍性を使い、条件を明示して比較する。

## 規約と注意
公開宣言の仮定・宇宙・射のクラスを維持する。個別の同型・squareの存在から、分解変更の完全なcoherenceを結論しない。

## 使われ方
局所入口Derived/BimoduleLocal.leanからは未使用。局所導来合成の計算部品、一般Morita・相対tensor・Hochschild型構成での作用と符号の比較に使える。
棚卸しと再開条件はformalization-plans/dg-theory-u12e-general-inventory.mdを参照。
-/
@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v w z
namespace SerrePositivity.DifferentialGraded.BalancedTensor
open CategoryTheory MonoidalCategory Opposite
variable (A : Type u) [CommRing A] (D : Type v) [DGCategory A D] [Small.{u} D]
  (E : Type w) [DGCategory A E] [Small.{u} E]
  (T : Type z) [DGCategory A T] [Small.{u} T]
  (F : DGFunctor A D E) (G : DGFunctor A E T)

/-- 二段階の指定増大を、合成関手に沿う制限への一つの増大へ束ねる。 -/
def resolvedRestrictionAugmentationComp
    {S : ModuleCategory A D} {R : ModuleCategory A E} {M : ModuleCategory A T}
    (r : S ⟶ (moduleRestriction A D E F.op).obj R)
    (q : R ⟶ (moduleRestriction A E T G.op).obj M) :
    S ⟶ (moduleRestriction A D T (F.comp G).op).obj M :=
  r ≫ (moduleRestriction A D E F.op).map q ≫
    (moduleRestrictionCompObjIso A D E T F.op G.op M).hom

@[simp]
lemma resolvedRestrictionAugmentationComp_eval
    {S : ModuleCategory A D} {R : ModuleCategory A E} {M : ModuleCategory A T}
    (r : S ⟶ (moduleRestriction A D E F.op).obj R)
    (q : R ⟶ (moduleRestriction A E T G.op).obj M) (d : D) :
    (moduleEvaluation A D d).map (resolvedRestrictionAugmentationComp A D E T F G r q) =
      (moduleEvaluation A D d).map r ≫ (moduleEvaluation A E (F.obj d)).map q := by
  simp only [resolvedRestrictionAugmentationComp, CategoryTheory.Functor.map_comp,
    moduleRestrictionCompObjIso_hom_eval, moduleRestriction_map_eval, Category.comp_id]
  rfl

lemma resolvedRestrictionAugmentationComp_quasiIso
    {S : ModuleCategory A D} {R : ModuleCategory A E} {M : ModuleCategory A T}
    (r : S ⟶ (moduleRestriction A D E F.op).obj R)
    (q : R ⟶ (moduleRestriction A E T G.op).obj M)
    (hr : moduleQuasiIso A D r) (hq : moduleQuasiIso A E q) :
    moduleQuasiIso A D (resolvedRestrictionAugmentationComp A D E T F G r q) := by
  intro d
  rw [resolvedRestrictionAugmentationComp_eval]
  have : QuasiIso ((moduleEvaluation A D d).map r) := hr d
  have : QuasiIso ((moduleEvaluation A E (F.obj d)).map q) := hq (F.obj d)
  exact quasiIso_comp _ _

omit [Small.{u} D] [Small.{u} E] [Small.{u} T] in
lemma restrictionLeft_comp_assoc (N : LeftModule A T) :
    F.comp (G.comp N) = (F.comp G).comp N := by
  apply EnrichedFunctor.ext (Complex A) (fun _ => rfl)
  intro x y
  simp only [eqToHom_refl, Category.comp_id]

/-- 同じ制限後モデルを保ち、左作用の反復制限表示だけを替える同型。 -/
def resolvedRestrictionCompTensorIso (S : RightModule A D) (N : LeftModule A T) :
    obj A D S (F.comp (G.comp N)) ≅ obj A D S ((F.comp G).comp N) :=
  changeLeft A D S (restrictionLeft_comp_assoc A D E T F G N)

omit [Small.{u} E] [Small.{u} T] in
@[reassoc]
lemma ι_resolvedRestrictionCompTensorIso_hom (S : RightModule A D) (N : LeftModule A T) (d : D) :
    ι A D S (F.comp (G.comp N)) d ≫ (resolvedRestrictionCompTensorIso A D E T F G S N).hom =
      ι A D S ((F.comp G).comp N) d :=
  (ι_changeLeft_hom A D S (restrictionLeft_comp_assoc A D E T F G N) d).trans
    (Category.id_comp _)

/-- 指定モデルと増大を使う二段階の実際の比較は、合成関手による一段階の比較と一致。 -/
lemma resolvedRestrictionComparison_comp
    {S : ModuleCategory A D} {R : ModuleCategory A E} {M : ModuleCategory A T}
    (r : S ⟶ (moduleRestriction A D E F.op).obj R)
    (q : R ⟶ (moduleRestriction A E T G.op).obj M) (N : LeftModule A T) :
    (resolvedRestrictionCompTensorIso A D E T F G
      (ForgetEnrichment.to (Complex A) S) N).hom ≫
        resolvedRestrictionComparison A D T (F.comp G)
          (resolvedRestrictionAugmentationComp A D E T F G r q) N =
      resolvedRestrictionComparison A D E F r (G.comp N) ≫
        resolvedRestrictionComparison A E T G q N := by
  apply hom_ext A D (ForgetEnrichment.to (Complex A) S) (F.comp (G.comp N))
  intro d
  rw [ι_resolvedRestrictionCompTensorIso_hom_assoc, ι_resolvedRestrictionComparison,
    ι_resolvedRestrictionComparison_assoc, ι_resolvedRestrictionComparison,
    resolvedRestrictionAugmentationComp_eval]
  let rd : (ForgetEnrichment.to (Complex A) S).obj (op d) ⟶
      (ForgetEnrichment.to (Complex A) R).obj (op (F.obj d)) :=
    (moduleEvaluation A D d).map r
  let qd : (ForgetEnrichment.to (Complex A) R).obj (op (F.obj d)) ⟶
      (ForgetEnrichment.to (Complex A) M).obj (op (G.obj (F.obj d))) :=
    (moduleEvaluation A E (F.obj d)).map q
  change ((rd ≫ qd) ⊗ₘ 𝟙 (N.obj (G.obj (F.obj d)))) ≫
      ι A T (ForgetEnrichment.to (Complex A) M) N (G.obj (F.obj d)) =
    (rd ⊗ₘ 𝟙 (N.obj (G.obj (F.obj d)))) ≫
      (qd ⊗ₘ 𝟙 (N.obj (G.obj (F.obj d)))) ≫
        ι A T (ForgetEnrichment.to (Complex A) M) N (G.obj (F.obj d))
  rw [tensorHom_comp_tensorHom_assoc, Category.comp_id]

end SerrePositivity.DifferentialGraded.BalancedTensor
