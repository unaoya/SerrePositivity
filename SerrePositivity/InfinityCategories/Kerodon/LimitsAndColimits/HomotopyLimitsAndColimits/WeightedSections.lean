module

public import Mathlib.AlgebraicTopology.SimplicialSet.Homotopy
public import Mathlib.CategoryTheory.Enriched.FunctorCategory
public import Mathlib.CategoryTheory.Monoidal.Closed.Enrichment
public import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
概要：単体集合の図式の重み付き切断空間を、内部 Hom の end として構成する。
方針：Mathlib の豊穣 end の普遍性と curry の自然性を使う。
規約：重み W と図式 H は同じ小圏上の共変図式。Kan 性は定義に不要。
使われ方：Kerodon 7.5.1.1（Tag 03A0）、7.5.4.6（Tag 03BB） の Bousfield–Kan 型の模型。

対応節は Kerodon 7.5（Tag 039Y）。
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory Limits MonoidalCategory MonoidalClosed CartesianMonoidalCategory SSet
open scoped MonoidalClosed Simplicial

namespace SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits

variable {I : Type u} [SmallCategory I]

/-- 概要：重み W から H への単体的自然変換の空間。
方針：内部 Hom の end を取る。
規約：各単体は W_i とパラメーターとの直積から H_i への自然な射の族を表す。
使われ方：Kerodon 7.5.1.1（Tag 03A0） の homotopy 極限の重み付き end 表示。 -/
noncomputable def weightedSections (W H : I ⥤ SSet.{u}) : SSet.{u} :=
  Enriched.FunctorCategory.enrichedHom SSet.{u} W H

/-- 概要：重み付き切断を各添字の内部 Hom へ射影する。
方針：end の射影を使う。
規約：i における値は Fun(W_i,H_i)。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の錐の成分との比較。 -/
noncomputable def weightedSectionsπ (W H : I ⥤ SSet.{u}) (i : I) :
    weightedSections W H ⟶ (ihom (W.obj i)).obj (H.obj i) :=
  Enriched.FunctorCategory.enrichedHomπ SSet.{u} W H i

/-- 概要：各内部 Hom への射影は図式の射に整合する。
方針：end の整合条件を内部 Hom の前合成と後合成で書き直す。
規約：重みも図式も共変。
使われ方：Kerodon 7.5.1.1（Tag 03A0） の重み付き切断の自然性。 -/
lemma weightedSections_condition (W H : I ⥤ SSet.{u}) {i j : I} (f : i ⟶ j) :
    weightedSectionsπ W H i ≫ (ihom (W.obj i)).map (H.map f) =
      weightedSectionsπ W H j ≫ (pre (W.map f)).app (H.obj j) := by
  dsimp only [weightedSectionsπ, weightedSections]
  simpa only [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
    enrichedOrdinaryCategorySelf_eHomWhiskerRight] using
    Enriched.FunctorCategory.enrichedHom_condition SSet.{u} W H f

/-- 概要：重み付き切断空間への射は全ての成分で決まる。
方針：end の射の外延性を使う。
規約：任意の単体集合 A を始域とする。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の比較射の自然性と成分の計算。 -/
lemma weightedSections_hom_ext {W H : I ⥤ SSet.{u}} {A : SSet.{u}}
    {f g : A ⟶ weightedSections W H}
    (h : ∀ i, f ≫ weightedSectionsπ W H i = g ≫ weightedSectionsπ W H i) : f = g :=
  end_.hom_ext h

/-- 概要：パラメーター付きの自然変換から重み付き切断への射を作る。
方針：各成分を curry し、自然性を end の条件へ移す。
規約：直積の左因子は重み、右因子はパラメーター A。
使われ方：Kerodon 7.5.1.1（Tag 03A0）、strict な錐からの比較射の構成。 -/
noncomputable def weightedSectionsLift {W H : I ⥤ SSet.{u}} {A : SSet.{u}}
    (s : W ⊗ (Functor.const I).obj A ⟶ H) : A ⟶ weightedSections W H :=
  end_.lift (fun i ↦ curry (s.app i)) (fun i j f ↦ by
    change curry (s.app i) ≫ eHomWhiskerLeft SSet.{u} (W.obj i) (H.map f) =
      curry (s.app j) ≫ eHomWhiskerRight SSet.{u} (W.map f) (H.obj j)
    rw [enrichedOrdinaryCategorySelf_eHomWhiskerLeft,
      enrichedOrdinaryCategorySelf_eHomWhiskerRight,
      ← curry_natural_right, curry_pre_app]
    apply congrArg curry
    simpa using (s.naturality f).symm)

/-- 概要：重み付き切断への持ち上げの各成分は元の成分を curry した射。
方針：end の持ち上げの射影を計算する。
規約：等式は単体集合の射として厳密。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の比較射を成分で検証する。 -/
lemma weightedSectionsLift_π {W H : I ⥤ SSet.{u}} {A : SSet.{u}}
    (s : W ⊗ (Functor.const I).obj A ⟶ H) (i : I) :
    weightedSectionsLift s ≫ weightedSectionsπ W H i = curry (s.app i) :=
  end_.lift_π _ _ i

/-- 概要：重み付き切断への射をパラメーター付きの自然変換へ戻す。
方針：各成分を uncurry し、end の条件を自然性へ戻す。
規約：A の Kan 性は不要。
使われ方：Kerodon 7.5.1.1（Tag 03A0） の重み付き切断の普遍性。 -/
noncomputable def weightedSectionsUncurry {W H : I ⥤ SSet.{u}} {A : SSet.{u}}
    (f : A ⟶ weightedSections W H) : W ⊗ (Functor.const I).obj A ⟶ H where
  app i := uncurry (f ≫ weightedSectionsπ W H i)
  naturality i j g := by
    change (W.map g ▷ A) ≫ uncurry (f ≫ weightedSectionsπ W H j) =
      uncurry (f ≫ weightedSectionsπ W H i) ≫ H.map g
    rw [← uncurry_pre_app, ← uncurry_natural_right]
    apply congrArg uncurry
    rw [Category.assoc, Category.assoc, weightedSections_condition]

/-- 概要：持ち上げを uncurry すると元の自然変換に戻る。
方針：各成分で curry と uncurry の逆性を使う。
規約：自然変換全体の厳密な等式。
使われ方：Kerodon 7.5.1.1（Tag 03A0） の普遍性の一方の逆。 -/
lemma weightedSectionsUncurry_lift {W H : I ⥤ SSet.{u}} {A : SSet.{u}}
    (s : W ⊗ (Functor.const I).obj A ⟶ H) :
    weightedSectionsUncurry (weightedSectionsLift s) = s := by
  apply NatTrans.ext
  funext i
  change uncurry (weightedSectionsLift s ≫ weightedSectionsπ W H i) = s.app i
  rw [weightedSectionsLift_π, uncurry_curry]

/-- 概要：uncurry した自然変換を持ち上げると元の射に戻る。
方針：end の外延性と curry と uncurry の逆性を使う。
規約：全ての重みと図式に対して成立する。
使われ方：Kerodon 7.5.1.1（Tag 03A0） の普遍性の他方の逆。 -/
lemma weightedSectionsLift_uncurry {W H : I ⥤ SSet.{u}} {A : SSet.{u}}
    (f : A ⟶ weightedSections W H) :
    weightedSectionsLift (weightedSectionsUncurry f) = f := by
  apply weightedSections_hom_ext
  intro i
  rw [weightedSectionsLift_π]
  exact curry_uncurry _

/-- 概要：重み付き切断への射はパラメーター付き自然変換と同値。
方針：curry による持ち上げと成分ごとの uncurry を両逆として束縛する。
規約：Kan 性や図式の fibrancy を前提にしない通常の普遍性。
使われ方：Kerodon 7.5.4.6（Tag 03BB） の具体的な比較を構成する基盤。 -/
noncomputable def weightedSectionsHomEquiv (W H : I ⥤ SSet.{u}) (A : SSet.{u}) :
    (A ⟶ weightedSections W H) ≃ (W ⊗ (Functor.const I).obj A ⟶ H) where
  toFun := weightedSectionsUncurry
  invFun := weightedSectionsLift
  left_inv := weightedSectionsLift_uncurry
  right_inv := weightedSectionsUncurry_lift

/-- 概要：strict な錐は重みの変数を忘れることで重み付き切断を定める。
方針：直積の第二射影の後に錐の自然変換を合成し、end へ持ち上げる。
規約：重みの可縮性や図式の Kan 性を定義の仮定にしない。
使われ方：Kerodon 7.5.4.1（Tag 03B6）、strict 極限から homotopy 極限への比較射。 -/
noncomputable def weightedConeComparison (W : I ⥤ SSet.{u}) {H : I ⥤ SSet.{u}}
    (c : Cone H) : c.pt ⟶ weightedSections W H :=
  weightedSectionsLift (snd W ((Functor.const I).obj c.pt) ≫ c.π)

/-- 概要：strict な錐からの比較射の成分は、重みを忘れた錐の成分の curry。
方針：end の射影の計算を使う。
規約：比較射は選択された逆同値によるものではない。
使われ方：Kerodon 7.5.4.1（Tag 03B6） の標準比較の特定。 -/
lemma weightedConeComparison_π (W : I ⥤ SSet.{u}) {H : I ⥤ SSet.{u}}
    (c : Cone H) (i : I) :
    weightedConeComparison W c ≫ weightedSectionsπ W H i =
      curry (snd (W.obj i) c.pt ≫ c.π.app i) :=
  weightedSectionsLift_π _ i

/-- 概要：重みの頂点を固定して重み付き切断を評価する。
方針：内部 Hom の射影を uncurry し、指定した頂点と恒等射の組を代入する。
規約：添字ごとの評価であり、そのまま strict な錐を定めるとは主張しない。
使われ方：Kerodon 7.5.1.1（Tag 03A0） の切断の値と元の図式との比較。 -/
noncomputable def weightedSectionsEval (W H : I ⥤ SSet.{u}) (i : I)
    (w : (W.obj i).obj (Opposite.op ⦋0⦌)) : weightedSections W H ⟶ H.obj i :=
  lift (SSet.const w) (𝟙 (weightedSections W H)) ≫ uncurry (weightedSectionsπ W H i)

/-- 概要：strict な錐から作った切断を任意の重みの頂点で評価すると元の錐の成分。
方針：評価と前合成を交換し、比較射の成分の curry を uncurry で戻す。
規約：全ての重みの頂点で同じ成分となるのは strict な錐から作った切断の場合。
使われ方：Kerodon 7.5.4.1（Tag 03B6） の標準比較射の成分の回収。 -/
lemma weightedConeComparison_eval (W : I ⥤ SSet.{u}) {H : I ⥤ SSet.{u}}
    (c : Cone H) (i : I) (w : (W.obj i).obj (Opposite.op ⦋0⦌)) :
    weightedConeComparison W c ≫ weightedSectionsEval W H i w = c.π.app i := by
  let q := weightedConeComparison W c
  have h : q ≫ lift (SSet.const w) (𝟙 (weightedSections W H)) =
      lift (SSet.const w) (𝟙 c.pt) ≫ (W.obj i ◁ q) := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [SSet.comp_const]
  change q ≫ (lift (SSet.const w) (𝟙 _) ≫ uncurry (weightedSectionsπ W H i)) = _
  rw [← Category.assoc, h, Category.assoc, ← uncurry_natural_left]
  change lift (SSet.const w) (𝟙 c.pt) ≫
    uncurry (weightedConeComparison W c ≫ weightedSectionsπ W H i) = _
  rw [weightedConeComparison_π, uncurry_curry, ← Category.assoc, lift_snd, Category.id_comp]

end SerrePositivity.InfinityCategories.Kerodon.LimitsAndColimits.HomotopyLimitsAndColimits
