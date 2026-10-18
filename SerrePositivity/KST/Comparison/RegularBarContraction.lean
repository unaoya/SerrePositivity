module

public import SerrePositivity.KST.Comparison.RegularBarProjection

/-!
# 正則 bar の対角収縮

概要：正則作用の自然な収縮を対角の単体集合へ移す。
方針：区間圏上の収縮関手の準同型に関する自然性を証明する。
規約：Segal 1974 Proposition 1.5。全空間の可縮性に群状性は不要。
使われ方：bar 射影のホモトピーファイバーとの比較。
-/

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u
namespace SerrePositivity.KST.Comparison
open CategoryTheory Opposite MonoidalCategory
open scoped Simplicial

/--
概要：正則作用の対象間の等式からの射は単位ラベルを持つ。
方針：等式帰納法で恒等射に帰着する。
規約：Segal 1974 Proposition 1.5 の全空間の自然性計算。
使われ方：関手の対象の等式による輸送を除く。
-/
@[simp] theorem regularAction_eqToHom_val {M : Type u} [Monoid M]
    {a b : RegularAction M} (h : a = b) : (eqToHom h).val = 1 := by
  cases h
  rfl

/--
概要：恒等射のラベルは単位である。
方針：正則作用の圏構造を評価する。
規約：Segal 1974 Proposition 1.5 のラベル計算。
使われ方：収縮の自然性。
-/
@[simp] theorem regularAction_id_val {M : Type u} [Monoid M] (a : RegularAction M) :
    (𝟙 a : a ⟶ a).val = 1 := rfl

/--
概要：合成のラベルは後の射と先の射のラベルの積である。
方針：正則作用の合成の定義を評価する。
規約：Segal 1974 Proposition 1.5。SingleObj と同じ順序。
使われ方：輸送を含む関手の自然性。
-/
@[simp] theorem regularAction_comp_val {M : Type u} [Monoid M]
    {a b c : RegularAction M} (f : a ⟶ b) (g : b ⟶ c) :
    (f ≫ g).val = g.val * f.val := rfl

/--
概要：正則作用の収縮を区間圏上の関手として表す。
方針：単位から恒等関手への自然変換を uncurry する。
規約：Segal 1974 Proposition 1.5 の全空間の収縮。
使われ方：全単体次数で整合する収縮。
-/
abbrev regularActionInterval (M : Type u) [Monoid M] : Fin 2 × RegularAction M ⥤ RegularAction M :=
  NerveHomotopy.interval (regularActionContraction (M := M))

/--
概要：収縮の区間関手はモノイド準同型と可換である。
方針：区間の三つの射の場合に分けてラベルを比較する。
規約：Segal 1974 Proposition 1.5。単位の保存の輸送も明示する。
使われ方：正則 bar の対角収縮の自然性。
-/
theorem regularActionInterval_map {M N : Type u} [Monoid M] [Monoid N] (f : M →* N) :
    (𝟭 (Fin 2)).prod (regularActionMap f) ⋙ regularActionInterval N =
      regularActionInterval M ⋙ regularActionMap f := by
  refine CategoryTheory.Functor.ext (fun x => ?_) ?_
  · rcases x with ⟨i, a⟩
    fin_cases i
    · exact congrArg RegularAction.mk (map_one f).symm
    · rfl
  · rintro ⟨i, a⟩ ⟨j, b⟩ h
    apply Subtype.ext
    fin_cases i <;> fin_cases j
    all_goals first
    | exact False.elim (by have hle : (1 : Fin 2) ≤ 0 := leOfHom h.1; simp at hle)
    | simp [regularActionInterval, NerveHomotopy.interval, Functor.uncurry,
      regularActionMap, regularActionContraction, ComposableArrows.mk₁,
      regularAction_comp_val]
/--
概要：正則 bar の対角上の収縮の区間写像。
方針：各次数の nerve の収縮を使い、区間関手の自然性で単体作用と交換する。
規約：Segal 1974 Proposition 1.5。群状性を仮定しない。
使われ方：全空間の可縮性の実ホモトピー。
-/
noncomputable def regularBarContractionMap (M : SimplicialObject MonCat.{u}) :
    regularBar M ⊗ (Δ[1] : SSet.{u}) ⟶ regularBar M where
  app n := (NerveHomotopy.hom (regularActionContraction (M := M.obj n))).app n
  naturality i j f := by
    apply ConcreteCategory.hom_ext
    intro p
    let α := (SimplexCategory.toCat.map f.unop).toFunctor
    let β := (SSet.stdSimplex.objEquiv p.2).toOrderHom.monotone.functor
    let F := regularActionMap (M.map f).hom
    symm
    change α ⋙ β.prod' p.1 ⋙ regularActionInterval (M.obj i) ⋙ F =
      α ⋙ β.prod' p.1 ⋙ (𝟭 (Fin 2)).prod F ⋙ regularActionInterval (M.obj j)
    exact congrArg (fun K => α ⋙ β.prod' p.1 ⋙ K)
      (regularActionInterval_map (M.map f).hom).symm

/--
概要：正則 bar の単位元の基点。
方針：零次モノイドの単位を正則作用の対象として選ぶ。
規約：Segal 1974 Proposition 1.5 の全空間の収縮先。
使われ方：対角収縮の定数写像。
-/
def regularBarBasepoint (M : SimplicialObject MonCat.{u}) : (regularBar M) _⦋0⦌ :=
  ComposableArrows.mk₀ (RegularAction.mk 1)

/--
概要：正則 bar の収縮の一端点は恒等写像である。
方針：区間の一端点で収縮関手を評価する。
規約：Segal 1974 Proposition 1.5 の可縮性。
使われ方：収縮の終点条件。
-/
theorem regularBarContractionMap_one (M : SimplicialObject MonCat.{u}) :
    SSet.ι₁ ≫ regularBarContractionMap M = 𝟙 (regularBar M) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro E
  refine CategoryTheory.Functor.ext (fun _ => rfl) ?_
  intro i j f
  change 𝟙 _ ≫ E.map f = eqToHom rfl ≫ E.map f ≫ eqToHom rfl
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/--
概要：正則 bar の収縮の零端点は単位元の基点への定数写像である。
方針：各次数の単位の像を準同型の単位保存で同定する。
規約：Segal 1974 Proposition 1.5。外側の次数も同時に評価する。
使われ方：対角収縮の始点条件。
-/
theorem regularBarContractionMap_zero (M : SimplicialObject MonCat.{u}) :
    SSet.ι₀ ≫ regularBarContractionMap M = SSet.const (regularBarBasepoint M) := by
  apply NatTrans.ext
  funext n
  apply ConcreteCategory.hom_ext
  intro E
  change ((SSet.ι₀ ≫ NerveHomotopy.hom
    (regularActionContraction (M := M.obj n))).app n) E = _
  rw [NerveHomotopy.at_zero]
  change E ⋙ (Functor.const (RegularAction (M.obj n))).obj ⟨1⟩ =
    (SimplexCategory.toCat.map (SimplexCategory.const n.unop ⦋0⦌ 0)).toFunctor ⋙
      (Functor.const (Fin 1)).obj (RegularAction.mk (1 : M.obj (op ⦋0⦌))) ⋙
        regularActionMap (M.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom
  refine CategoryTheory.Functor.ext (fun _ => ?_) ?_
  · exact congrArg RegularAction.mk (map_one
      (M.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom).symm
  · intro i j f
    apply Subtype.ext
    simp only [regularAction_comp_val, regularAction_eqToHom_val, one_mul, mul_one]
    change (1 : M.obj n) = (M.map (SimplexCategory.const n.unop ⦋0⦌ 0).op).hom 1
    exact (map_one _).symm


/--
概要：正則 bar の対角の全空間を単位元へ収縮する実単体的ホモトピー。
方針：各次数の区間関手の自然性と二つの端点条件を束ねる。
規約：Segal 1974 Proposition 1.5。群状性は使わない。
使われ方：普遍 bar 束の全空間の可縮性。
-/
noncomputable def regularBarContraction (M : SimplicialObject MonCat.{u}) :
    SSet.Homotopy (SSet.const (X := regularBar M) (regularBarBasepoint M))
      (𝟙 (regularBar M)) where
  h := regularBarContractionMap M
  h₀ := regularBarContractionMap_zero M
  h₁ := regularBarContractionMap_one M
  rel := by
    apply NatTrans.ext
    funext n
    apply ConcreteCategory.hom_ext
    intro x
    exact False.elim x.1.property


end SerrePositivity.KST.Comparison
