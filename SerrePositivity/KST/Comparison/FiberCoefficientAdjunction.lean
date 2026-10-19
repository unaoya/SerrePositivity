module

public import SerrePositivity.KST.Comparison.LocalCoefficientOverFunctor
public import Mathlib.CategoryTheory.Adjunction.Basic

/-!
# 係数群の族に対する直和の随伴

概要：基底の各点の係数群を引き戻して直和を取る関手の左随伴性を構成する。
方針：準同型の集合を各基底点で束ねる射影との Hom 同値を使う。
規約：Weibel K-book IV.1.6 の局所係数の次数ごとの模型。
使われ方：基底上の局所係数鎖複体の余極限保存。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory CategoryTheory.Limits

/--
概要：係数群からの準同型を基底の全ての点で束ねる関手。
方針：G に対して Σ b, Hom(A_b,G) の基底への射影を取る。
規約：基底上の型の圏に値を取る。
使われ方：係数群の直和を取る関手の右随伴。
-/
def fiberCoefficientHomFunctor (T : Type u) (A : T → AddCommGrpCat.{u}) :
    AddCommGrpCat.{u} ⥤ Over T where
  obj G := Over.mk (↾fun x : Σ b : T, A b ⟶ G => x.1)
  map f := Over.homMk (↾fun x => ⟨x.1, x.2 ≫ f⟩) rfl
  map_id G := by
    apply Over.OverMorphism.ext
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨b, h⟩
    apply Sigma.ext rfl
    exact heq_of_eq (Category.comp_id h)
  map_comp f g := by
    apply Over.OverMorphism.ext
    apply ConcreteCategory.hom_ext
    intro x
    rcases x with ⟨b, h⟩
    apply Sigma.ext rfl
    exact heq_of_eq (Category.assoc h f g).symm

/--
概要：基底上の準同型の族の写像は基底点を保つ。
方針：slice の射の可換性を元で評価する。
規約：右随伴の射影への写像。
使われ方：直和の普遍性の逆写像での係数の輸送。
-/
theorem fiberCoefficientProjection_eq {T : Type u} (A : T → AddCommGrpCat.{u})
    {p : Over T} {G : AddCommGrpCat.{u}} (f : p ⟶ (fiberCoefficientHomFunctor T A).obj G)
    (x : p.left) : (f.left x).1 = p.hom x :=
  congrArg (fun q : p.left ⟶ T => q x) f.w

/--
概要：直和からの準同型を基底上の準同型の族へ送る。
方針：各直和成分の包含との合成を取る。
規約：基底点は p が指定する点。
使われ方：随伴の Hom 同値の順方向。
-/
def fiberCoefficientLift {T : Type u} (A : T → AddCommGrpCat.{u}) (p : Over T)
    (G : AddCommGrpCat.{u}) (h : (∐ fun x : p.left => A (p.hom x)) ⟶ G) :
    p ⟶ (fiberCoefficientHomFunctor T A).obj G :=
  Over.homMk (↾fun x => ⟨p.hom x, Sigma.ι (fun x : p.left => A (p.hom x)) x ≫ h⟩) rfl

/--
概要：基底上の準同型の族から直和上の準同型を構成する。
方針：可換性による基底点の等式で係数を輸送し、直和の普遍性を使う。
規約：等式の輸送を省略しない。
使われ方：随伴の Hom 同値の逆方向。
-/
def fiberCoefficientDesc {T : Type u} (A : T → AddCommGrpCat.{u}) (p : Over T)
    (G : AddCommGrpCat.{u}) (f : p ⟶ (fiberCoefficientHomFunctor T A).obj G) :
    (∐ fun x : p.left => A (p.hom x)) ⟶ G :=
  Sigma.desc (fun x =>
    eqToHom (congrArg A (fiberCoefficientProjection_eq A f x).symm) ≫ (f.left x).2)

/--
概要：基底点の等式に沿って係数を戻した準同型は元の族の元を復元する。
方針：族の元と等式を帰納し、恒等射との合成へ帰着する。
規約：等式の輸送による復元。
使われ方：Hom 同値の逆方向の合成の計算。
-/
theorem fiberCoefficientSigmaReassemble {T : Type u} (A : T → AddCommGrpCat.{u})
    (G : AddCommGrpCat.{u}) (x : Σ b : T, A b ⟶ G) (b : T) (h : x.1 = b) :
    (⟨b, eqToHom (congrArg A h.symm) ≫ x.2⟩ : Σ b : T, A b ⟶ G) = x := by
  rcases x with ⟨a, g⟩
  dsimp at h
  subst b
  simp

/--
概要：引き戻した係数群の直和からの準同型と、基底上の準同型の族の写像の同値。
方針：直和の普遍性を両方向に使い、可換性からの等式の輸送を照合する。
規約：任意の係数群の族。
使われ方：実際の左随伴関手の構成。
-/
def fiberCoefficientHomEquiv {T : Type u} (A : T → AddCommGrpCat.{u}) (p : Over T)
    (G : AddCommGrpCat.{u}) :
    ((∐ fun x : p.left => A (p.hom x)) ⟶ G) ≃
      (p ⟶ (fiberCoefficientHomFunctor T A).obj G) where
  toFun := fiberCoefficientLift A p G
  invFun := fiberCoefficientDesc A p G
  left_inv h := by
    apply Sigma.hom_ext
    intro x
    simp [fiberCoefficientDesc, fiberCoefficientLift]
    rfl
  right_inv f := by
    apply Over.OverMorphism.ext
    apply ConcreteCategory.hom_ext
    intro x
    change (⟨p.hom x, Sigma.ι (fun x : p.left => A (p.hom x)) x ≫
      fiberCoefficientDesc A p G f⟩ : Σ b : T, A b ⟶ G) = f.left x
    have hh : Sigma.ι (fun x : p.left => A (p.hom x)) x ≫ fiberCoefficientDesc A p G f =
        eqToHom (congrArg A (fiberCoefficientProjection_eq A f x).symm) ≫ (f.left x).2 :=
      Sigma.ι_comp_desc _ x
    exact (congrArg (fun q : A (p.hom x) ⟶ G => (⟨p.hom x, q⟩ : Σ b : T, A b ⟶ G)) hh).trans
      (fiberCoefficientSigmaReassemble A G (f.left x) (p.hom x)
        (fiberCoefficientProjection_eq A f x))

/--
概要：直和と準同型の族の Hom 同値は標的のアーベル群に関して自然である。
方針：各直和包含との合成の結合法則を使う。
規約：標的の準同型による後合成。
使われ方：左随伴関手の構成条件。
-/
theorem fiberCoefficientHomEquiv_naturality {T : Type u} (A : T → AddCommGrpCat.{u})
    (p : Over T) {G H : AddCommGrpCat.{u}} (g : G ⟶ H)
    (h : (∐ fun x : p.left => A (p.hom x)) ⟶ G) :
    fiberCoefficientHomEquiv A p H (h ≫ g) =
      fiberCoefficientHomEquiv A p G h ≫ (fiberCoefficientHomFunctor T A).map g := by
  apply Over.OverMorphism.ext
  apply ConcreteCategory.hom_ext
  intro x
  change (⟨p.hom x, Sigma.ι (fun x : p.left => A (p.hom x)) x ≫ (h ≫ g)⟩ :
      Σ b : T, A b ⟶ H) =
    ⟨p.hom x, (Sigma.ι (fun x : p.left => A (p.hom x)) x ≫ h) ≫ g⟩
  exact congrArg (fun q : A (p.hom x) ⟶ H => (⟨p.hom x, q⟩ : Σ b : T, A b ⟶ H))
    (Category.assoc _ _ _).symm

/--
概要：基底上の型から、その各点の係数群の直和への関手。
方針：構成した Hom 同値から左随伴の射への作用と関手法則を作る。
規約：対象 p:X→T では ⊕_x A_(p x)。
使われ方：各単体次数の局所係数の余極限保存。
-/
def fiberCoefficientFunctor (T : Type u) (A : T → AddCommGrpCat.{u}) :
    Over T ⥤ AddCommGrpCat.{u} :=
  Adjunction.leftAdjointOfEquiv (fun p G => fiberCoefficientHomEquiv A p G)
    (fun p _ _ g h => fiberCoefficientHomEquiv_naturality A p g h)

/--
概要：基底上の型の係数の直和は、準同型の族の関手の左随伴である。
方針：実際の Hom 同値とその自然性を随伴へまとめる。
規約：余極限保存を追加の仮定にしない。
使われ方：局所係数の鎖群の余極限保存。
-/
def fiberCoefficientAdjunction (T : Type u) (A : T → AddCommGrpCat.{u}) :
    fiberCoefficientFunctor T A ⊣ fiberCoefficientHomFunctor T A :=
  Adjunction.adjunctionOfEquivLeft (fun p G => fiberCoefficientHomEquiv A p G)
    (fun p _ _ g h => fiberCoefficientHomEquiv_naturality A p g h)

/--
概要：係数の直和を取る関手は左随伴である。
方針：構成した具体的な随伴を登録する。
規約：全ての指定宇宙の余極限に適用できる。
使われ方：余極限保存の型クラス。
-/
instance fiberCoefficientFunctor_isLeftAdjoint (T : Type u) (A : T → AddCommGrpCat.{u}) :
    (fiberCoefficientFunctor T A).IsLeftAdjoint :=
  ⟨_, ⟨fiberCoefficientAdjunction T A⟩⟩

end SerrePositivity.KST.Comparison
