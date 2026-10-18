module

public import Mathlib.Algebra.Category.ModuleCat.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
概要：元の係数環上の加群値で局所化関手とその完全性を構成する。
方針：LocalizedModule の R 加群構造と線形写像の普遍的延長を使う。
規約：Čech 各項の比較で元の R 線形性を保持する。
使われ方：TT §3、Toën §3.2 の基本開切断の局所化と Čech 比較。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {R : Type u} [CommRing R] (S : Submonoid R)

/--
概要：局所化を元の R 加群の圏の自己関手として扱う。
方針：局所化加群と線形写像の普遍的延長をそのまま束ねる。
規約：元と同じ宇宙の加群を扱う。
使われ方：TT §3、Toën §3.2 の Čech 切断の局所化。
-/
def moduleLocalizationR : ModuleCat.{u} R ⥤ ModuleCat.{u} R where
  obj M := ModuleCat.of R (LocalizedModule S M)
  map {M N} f := ModuleCat.ofHom
    (IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S N) f.hom)
  map_id M := by
    ext x
    exact congrArg (fun l => l x) (IsLocalizedModule.map_id S (LocalizedModule.mkLinearMap S M))
  map_comp {M N L} f g := by
    ext x
    exact congrArg (fun l => l x) (IsLocalizedModule.map_comp' S
      (LocalizedModule.mkLinearMap S M) (LocalizedModule.mkLinearMap S N)
      (LocalizedModule.mkLinearMap S L) f.hom g.hom)

/--
概要：R 加群値の局所化関手は加法的。
方針：局所化写像の線形延長の加法性を使う。
規約：対象上の R 加群構造を変えない。
使われ方：TT §3、Toën §3.2 の複体の局所化。
-/
instance moduleLocalizationR_additive : (moduleLocalizationR S).Additive where
  map_add {M N f g} := by
    ext x
    exact congrArg (fun l : LocalizedModule S M →ₗ[R] LocalizedModule S N => l x)
      ((IsLocalizedModule.map S (LocalizedModule.mkLinearMap S M)
        (LocalizedModule.mkLinearMap S N)).map_add f.hom g.hom)

/--
概要：R 加群値の局所化は短複体の完全性を保つ。
方針：局所化加群の線形写像の完全性の定理を使う。
規約：加群の有限生成性は要求しない。
使われ方：TT §3、Toën §3.2 の Čech 微分の局所化。
-/
lemma moduleLocalizationR_map_exact (T : ShortComplex (ModuleCat.{u} R)) (hT : T.Exact) :
    (T.map (moduleLocalizationR S)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
  exact IsLocalizedModule.map_exact S (LocalizedModule.mkLinearMap S T.X₁)
    (LocalizedModule.mkLinearMap S T.X₂) (LocalizedModule.mkLinearMap S T.X₃) _ _ hT

/--
概要：R 加群値の局所化は有限極限を保つ。
方針：証明済みの短複体の完全性保存を適用する。
規約：有限積の比較もこの構造から得る。
使われ方：TT §3、Toën §3.2 の有限被覆の Čech 各項。
-/
instance moduleLocalizationR_preservesFiniteLimits : PreservesFiniteLimits (moduleLocalizationR S) := by
  have h : PreservesFiniteLimits (moduleLocalizationR S) ∧
      PreservesFiniteColimits (moduleLocalizationR S) :=
    ((Functor.exact_tfae (moduleLocalizationR S)).out 2 4).mp (moduleLocalizationR_map_exact S)
  exact h.1

/--
概要：R 加群値の局所化は有限余極限を保つ。
方針：証明済みの短複体の完全性保存を適用する。
規約：元の加群圏の余核を比較する。
使われ方：TT §3、Toën §3.2 の複体の局所化。
-/
instance moduleLocalizationR_preservesFiniteColimits :
    PreservesFiniteColimits (moduleLocalizationR S) := by
  have h : PreservesFiniteLimits (moduleLocalizationR S) ∧
      PreservesFiniteColimits (moduleLocalizationR S) :=
    ((Functor.exact_tfae (moduleLocalizationR S)).out 2 4).mp (moduleLocalizationR_map_exact S)
  exact h.2

/--
概要：R 加群値の局所化の単位は自然変換。
方針：局所化写像と線形写像の延長の生成元の公式を使う。
規約：加群圏の射として束ねる。
使われ方：TT §3、Toën §3.2 の切断比較の自然性。
-/
def moduleLocalizationR_unit : 𝟭 (ModuleCat.{u} R) ⟶ moduleLocalizationR S where
  app M := ModuleCat.ofHom (X := M) (Y := (moduleLocalizationR S).obj M)
    (LocalizedModule.mkLinearMap S M)
  naturality {M N} f := by
    ext x
    exact (IsLocalizedModule.map_apply S (LocalizedModule.mkLinearMap S M)
      (LocalizedModule.mkLinearMap S N) f.hom x).symm

/--
概要：局所化後に延長できる加群圏の射を実際に構成する。
方針：局所化の普遍的な線形延長を加群圏の射として束ねる。
規約：元の R 線形性を保持する。
使われ方：TT §3、Toën §3.2 の切断の局所化比較。
-/
def moduleLocalizationR_lift {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hN : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s.val)) :
    (moduleLocalizationR S).obj M ⟶ N :=
  ModuleCat.ofHom (X := (moduleLocalizationR S).obj M) (Y := N)
    (IsLocalizedModule.lift (M' := LocalizedModule S M) (M'' := N)
      S (LocalizedModule.mkLinearMap S M) f.hom hN)

/--
概要：加群圏の局所化の延長は単位との合成で元の射に戻る。
方針：普遍的延長の合成公式を使う。
規約：等式は加群圏の射の等式。
使われ方：TT §3、Toën §3.2 の切断比較の生成元の計算。
-/
lemma moduleLocalizationR_unit_lift {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hN : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s.val)) :
    (moduleLocalizationR_unit S).app M ≫ moduleLocalizationR_lift S f hN = f := by
  ext x
  exact IsLocalizedModule.lift_apply S (LocalizedModule.mkLinearMap S M) f.hom hN x

/--
概要：元の写像も局所化なら、その普遍的延長は同型。
方針：同じ加群の二つの局所化の比較の同型判定を使う。
規約：同型の存在を追加のフィールドにしない。
使われ方：TT §3、Toën §3.2 の基本開切断の比較同型。
-/
lemma moduleLocalizationR_lift_isIso {M N : ModuleCat.{u} R} (f : M ⟶ N)
    (hN : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s.val))
    [IsLocalizedModule S f.hom] : IsIso (moduleLocalizationR_lift S f hN) := by
  have h₁ : IsLocalizedModule S ((moduleLocalizationR_unit S).app M).hom := by
    change IsLocalizedModule S (LocalizedModule.mkLinearMap S M)
    infer_instance
  have heq := congrArg ModuleCat.Hom.hom (moduleLocalizationR_unit_lift S f hN)
  have h₂ : IsLocalizedModule S
      (((moduleLocalizationR_unit S).app M ≫ moduleLocalizationR_lift S f hN).hom) :=
    heq.symm ▸ inferInstance
  exact ModuleCat.isIso_of_isLocalizedModule_comp h₁ h₂

/--
概要：局所化からの射は単位上で一致すれば一致する。
方針：局所化の線形写像の一意性を加群圏へ移す。
規約：標的では S の作用の可逆性だけを要求する。
使われ方：TT §3、Toën §3.2 の比較の自然性。
-/
lemma moduleLocalizationR_hom_ext {M N : ModuleCat.{u} R}
    (hN : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s.val))
    {f g : (moduleLocalizationR S).obj M ⟶ N}
    (h : (moduleLocalizationR_unit S).app M ≫ f = (moduleLocalizationR_unit S).app M ≫ g) :
    f = g := by
  apply ModuleCat.hom_ext
  apply IsLocalizedModule.ext S (LocalizedModule.mkLinearMap S M) hN
  exact congrArg ModuleCat.Hom.hom h

/--
概要：局所化の普遍的延長は可換正方形と両立する。
方針：単位上で比較し、元の可換正方形と延長の一意性を使う。
規約：層や開集合から独立した加群圏の等式。
使われ方：TT §3、Toën §3.2 の Čech 微分との両立。
-/
lemma moduleLocalizationR_lift_naturality {M N M' N' : ModuleCat.{u} R}
    (f : M ⟶ N) (f' : M' ⟶ N') (α : M ⟶ M') (β : N ⟶ N')
    (hN : ∀ s : S, IsUnit (algebraMap R (Module.End R N) s.val))
    (hN' : ∀ s : S, IsUnit (algebraMap R (Module.End R N') s.val))
    (h : f ≫ β = α ≫ f') :
    (moduleLocalizationR S).map α ≫ moduleLocalizationR_lift S f' hN' =
      moduleLocalizationR_lift S f hN ≫ β := by
  apply moduleLocalizationR_hom_ext S hN'
  calc
    _ = α ≫ (moduleLocalizationR_unit S).app M' ≫ moduleLocalizationR_lift S f' hN' := by
      rw [← Category.assoc, ← (moduleLocalizationR_unit S).naturality α, Category.assoc]
      rfl
    _ = α ≫ f' := by rw [moduleLocalizationR_unit_lift]
    _ = f ≫ β := h.symm
    _ = _ := by rw [← Category.assoc, moduleLocalizationR_unit_lift]

end SerrePositivity.KST.DerivedGeometry
