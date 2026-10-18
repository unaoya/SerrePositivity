module

public import SerrePositivity.KST.Descent.BlowupBaseChangeCube
public import SerrePositivity.KST.Descent.FiniteTypeBaseChangeComparison

/-!
# 抽象 blowup の全基底射に関する底変換関手と自然な比較立方体

## 概要
実際の抽象 blowup の底変換正方形を関手にし、元の正方形への比較立方体を自然変換にする。

## 方針
指定された finiteTypePullback の map を使い、例外部分は新しい Cartesian 正方形へ持ち上げる。

## 規約
中心の厚みと実際の指定引き戻しを保持する。群ごとの列の自然性を追加公理にしない。

## 使われ方
論文 補題 3.3 の全 Čech 段での抽象 blowup の自然な比較。
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace SerrePositivity.KST.Descent

/-- 概要：終域の正方形が Cartesian なら三頂点の一致で正方形の射が一致（補題 3.3）。
方針：左上の射の一致を Cartesian 普遍性と二つの可換式で検査する。
規約：四つの射を持つ実際の正方形の射。使われ方：底変換立方体の関手性と自然性。 -/
theorem square_hom_ext_of_isPullback {C : Type u} [Category.{v} C] {Q R : Square C}
    (H : IsPullback R.f₁₂ R.f₁₃ R.f₂₄ R.f₃₄) {a b : Q ⟶ R}
    (h₂ : a.τ₂ = b.τ₂) (h₃ : a.τ₃ = b.τ₃) (h₄ : a.τ₄ = b.τ₄) : a = b := by
  apply Square.hom_ext ?_ h₂ h₃ h₄
  apply H.hom_ext
  · exact a.comm₁₂.symm.trans ((congrArg (Q.f₁₂ ≫ ·) h₂).trans b.comm₁₂)
  · exact a.comm₁₃.symm.trans ((congrArg (Q.f₁₃ ≫ ·) h₃).trans b.comm₁₃)

namespace AbstractBlowupSquare

variable {S : Scheme.{u}} [IsNoetherian S] (Q : AbstractBlowupSquare S)

/-- 概要：二つの底変換正方形の上辺・左辺から新しい例外部分への持ち上げの可換式（補題 3.3）。
方針：指定底変換 map の第二射影公式と元の正方形の可換式を合成する。
規約：実際の finiteTypePullback の map。使われ方：基底射から比較立方体を作る。 -/
theorem baseChange_map_fac {Z Z' : Over Q.square.X₄} (α : Z ⟶ Z') :
    ((Q.baseChange Z.hom).square.f₁₂ ≫ finiteTypeBaseChangeMap Q.square.f₂₄ α) ≫
        (Q.baseChange Z'.hom).square.f₂₄ =
      ((Q.baseChange Z.hom).square.f₁₃ ≫ finiteTypeBaseChangeMap Q.square.f₃₄ α) ≫
        (Q.baseChange Z'.hom).square.f₃₄ := by
  have hi :
      ((Q.baseChange Z.hom).square.f₁₃ ≫ finiteTypeBaseChangeMap Q.square.f₃₄ α) ≫
          (Q.baseChange Z'.hom).square.f₃₄ =
        ((Q.baseChange Z.hom).square.f₁₃ ≫ (Q.baseChange Z.hom).square.f₃₄) ≫ α.left :=
    (Category.assoc _ _ _).trans
      ((congrArg ((Q.baseChange Z.hom).square.f₁₃ ≫ ·)
        (finiteTypeBaseChangeMap_snd Q.square.f₃₄ α)).trans (Category.assoc _ _ _).symm)
  have hp :
      ((Q.baseChange Z.hom).square.f₁₂ ≫ finiteTypeBaseChangeMap Q.square.f₂₄ α) ≫
          (Q.baseChange Z'.hom).square.f₂₄ =
        ((Q.baseChange Z.hom).square.f₁₂ ≫ (Q.baseChange Z.hom).square.f₂₄) ≫ α.left :=
    (Category.assoc _ _ _).trans
      ((congrArg ((Q.baseChange Z.hom).square.f₁₂ ≫ ·)
        (finiteTypeBaseChangeMap_snd Q.square.f₂₄ α)).trans (Category.assoc _ _ _).symm)
  have hm :
      ((Q.baseChange Z.hom).square.f₁₂ ≫ (Q.baseChange Z.hom).square.f₂₄) ≫ α.left =
        ((Q.baseChange Z.hom).square.f₁₃ ≫ (Q.baseChange Z.hom).square.f₃₄) ≫ α.left :=
    congrArg (· ≫ α.left) (Q.baseChange Z.hom).square.fac
  exact hp.trans (hm.trans hi.symm)

/-- 概要：基底上の射が誘導する二つの実際の底変換正方形の比較立方体（補題 3.3）。
方針：三頂点に指定底変換の map を使い、左上は終域の Cartesian 正方形へ持ち上げる。
規約：全て同じ有限型の圏内。使われ方：Čech の全ての面射・退化射への底変換の作用。 -/
noncomputable def baseChangeMap {Z Z' : Over Q.square.X₄} (α : Z ⟶ Z') :
    (Q.baseChange Z.hom).square ⟶ (Q.baseChange Z'.hom).square where
  τ₁ := (Q.baseChange Z'.hom).isPullback.lift
    ((Q.baseChange Z.hom).square.f₁₂ ≫ finiteTypeBaseChangeMap Q.square.f₂₄ α)
    ((Q.baseChange Z.hom).square.f₁₃ ≫ finiteTypeBaseChangeMap Q.square.f₃₄ α)
    (Q.baseChange_map_fac α)
  τ₂ := finiteTypeBaseChangeMap Q.square.f₂₄ α
  τ₃ := finiteTypeBaseChangeMap Q.square.f₃₄ α
  τ₄ := α.left
  comm₁₂ := ((Q.baseChange Z'.hom).isPullback.lift_fst _ _ _).symm
  comm₁₃ := ((Q.baseChange Z'.hom).isPullback.lift_snd _ _ _).symm
  comm₂₄ := (finiteTypeBaseChangeMap_snd Q.square.f₂₄ α).symm
  comm₃₄ := (finiteTypeBaseChangeMap_snd Q.square.f₃₄ α).symm

/-- 概要：抽象 blowup の指定底変換 map は恒等射を保つ（補題 3.3）。
方針：三頂点で恒等射を検査し、左上の一意性を使う。
規約：実際の正方形の射の等式。使われ方：全 Čech 図式の関手性。 -/
@[simp] theorem baseChangeMap_id (Z : Over Q.square.X₄) :
    Q.baseChangeMap (𝟙 Z) = 𝟙 (Q.baseChange Z.hom).square := by
  apply square_hom_ext_of_isPullback (Q.baseChange Z.hom).isPullback
  · exact finiteTypeBaseChangeMap_id Q.square.f₂₄ Z
  · exact finiteTypeBaseChangeMap_id Q.square.f₃₄ Z
  · rfl

/-- 概要：抽象 blowup の指定底変換 map は合成を保つ（補題 3.3）。
方針：三頂点で指定 map の合成を検査し、左上の一意性を使う。
規約：全ての基底上の射に対して成立。使われ方：面射・退化射の全恒等式の保持。 -/
theorem baseChangeMap_comp {Z Z' Z'' : Over Q.square.X₄} (α : Z ⟶ Z') (β : Z' ⟶ Z'') :
    Q.baseChangeMap α ≫ Q.baseChangeMap β = Q.baseChangeMap (α ≫ β) := by
  apply square_hom_ext_of_isPullback (Q.baseChange Z''.hom).isPullback
  · exact finiteTypeBaseChangeMap_comp Q.square.f₂₄ α β
  · exact finiteTypeBaseChangeMap_comp Q.square.f₃₄ α β
  · rfl

/-- 概要：抽象 blowup の実際の底変換正方形の関手（補題 3.3）。
方針：指定正方形と map の恒等射・合成保存を使う。
規約：値は元の有限型の圏内の正方形。
使われ方：任意の Čech 図式に抽象 blowup 降下を段ごとに適用する。 -/
noncomputable def baseChangeFunctor : Over Q.square.X₄ ⥤ Square (FiniteTypeSchemes S) where
  obj Z := (Q.baseChange Z.hom).square
  map α := Q.baseChangeMap α
  map_id Z := Q.baseChangeMap_id Z
  map_comp α β := (Q.baseChangeMap_comp α β).symm

/-- 概要：実際の底変換から元の抽象 blowup への比較立方体は自然（補題 3.3）。
方針：指定 map の第一射影の保存と三頂点での一意性を使う。
規約：全ての基底上の射に対する自然変換。
使われ方：自然な抽象 blowup 列と Čech の全単体射を同時に扱う。 -/
noncomputable def baseChangeToOriginal :
    Q.baseChangeFunctor ⟶ (Functor.const (Over Q.square.X₄)).obj Q.square where
  app Z := Q.baseChangeCube Z.hom
  naturality {Z Z'} α := by
    apply square_hom_ext_of_isPullback Q.isPullback
    · exact (finiteTypeBaseChangeMap_fst Q.square.f₂₄ α).trans (Category.comp_id _).symm
    · exact (finiteTypeBaseChangeMap_fst Q.square.f₃₄ α).trans (Category.comp_id _).symm
    · exact α.w.trans (Category.comp_id _).symm

/-- 概要：全 Čech 段の実際の底変換された抽象 blowup 正方形（補題 3.3）。
方針：元の Over の Čech 図式へ正方形の底変換関手を合成する。
規約：全ての単体射と中心の厚みを保持する。
使われ方：同じ前層による抽象 blowup 降下と Čech の Fubini の幾何入力。 -/
noncomputable def cechBaseChangeSquares {V : FiniteTypeSchemes S} (cover : V ⟶ Q.square.X₄) :
    SimplexCategoryᵒᵖ ⥤ Square (FiniteTypeSchemes S) :=
  cechOverDiagram cover ⋙ Q.baseChangeFunctor

/-- 概要：Čech 全単体射に自然な元の抽象 blowup への比較立方体（補題 3.3）。
方針：全基底射に自然な比較を元の Čech 図式に制限する。
規約：段ごとに自然性を独立に仮定しない。
使われ方：Čech による元の正方形と全底変換列の比較。 -/
noncomputable def cechBaseChangeToOriginal {V : FiniteTypeSchemes S}
    (cover : V ⟶ Q.square.X₄) :
    Q.cechBaseChangeSquares cover ⟶ (Functor.const SimplexCategoryᵒᵖ).obj Q.square :=
  Functor.whiskerLeft (cechOverDiagram cover) Q.baseChangeToOriginal

end AbstractBlowupSquare

end SerrePositivity.KST.Descent
