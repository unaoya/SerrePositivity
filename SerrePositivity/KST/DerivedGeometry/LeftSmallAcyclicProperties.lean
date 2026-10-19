module

public import SerrePositivity.KST.DerivedGeometry.LeftSmallAcyclicComplex

/-!
概要：整数複体内に構成した小さい部分複体の非輪状性、単射性、有界性と項の上界。
方針：自然数方向で証明した性質を零延長の比較で移す。
規約：全ての性質を構成済みの実際の複体と包含について証明する。
使われ方：Stacks Lemma 19.12.2、TT §3・§8、Toën §3.2 の試験集合の構成。
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe w u
open CategoryTheory Limits
namespace SerrePositivity.KST.DerivedGeometry
variable {C : Type u} [Category.{w} C] [Abelian C] [IsGrothendieckAbelian.{w} C]
  (G : C) (hG : IsSeparator G) (M : CochainComplex C ℤ) (hM : M.Acyclic) (top : ℤ)
  (ψ : G ⟶ (M.restriction (ComplexShape.embeddingUpIntLE top)).X 1)

/--
概要：整数次数へ零延長した小さい部分複体は非輪状。
方針：自然数鎖複体の非輪状性と延長のコホモロジー比較を使う。
規約：全整数次数。
使われ方：Stacks 19.12.2、TT §3 の小さい非輪状試験族。
-/
lemma leftSmallAcyclicComplex_acyclic : (leftSmallAcyclicComplex G hG M hM top ψ).Acyclic :=
  extended_acyclic _ _ (smallExactChainTail_acyclic G hG _ _)

/--
概要：左制限への小さい鎖複体の包含は各項で単射。
方針：自然数方向の窓の包含の単射性を使う。
規約：全自然数次数。
使われ方：Stacks 19.12.2、TT §3 の整数部分複体への接続。
-/
instance leftSmallAcyclicChainInclusion_f_mono (n : ℕ) :
    Mono ((leftSmallAcyclicChainInclusion G hG M hM top ψ).f n) :=
  smallExactChainInclusion_f_mono _ _ _ _ n

/--
概要：整数部分複体の包含は各項で単射。
方針：零延長の射の成分での単射性の一般補題を使う。
規約：像の外は零対象からの射。
使われ方：Stacks 19.12.2、TT §3 の部分対象の実際の射。
-/
instance leftSmallAcyclicComplexInclusion_f_mono (n : ℤ) :
    Mono ((leftSmallAcyclicComplexInclusion G hG M hM top ψ).f n) :=
  descFromExtendedComplex_f_mono _ _ _ n

/--
概要：小さい非輪状部分複体の包含は複体の圏で単射。
方針：全成分の単射性を用いる。
規約：元の非有界複体の圏。
使われ方：Stacks 19.12.2、TT §3 の非輪状部分対象を加える超限工程。
-/
instance leftSmallAcyclicComplexInclusion_mono : Mono (leftSmallAcyclicComplexInclusion G hG M hM top ψ) :=
  HomologicalComplex.mono_of_mono_f _ (fun _ => inferInstance)

/--
概要：小さい非輪状部分複体は指定した上端より上で項が零。
方針：零延長の支持条件を使う。
規約：strict な複体の有界性。
使われ方：Stacks 19.12.2、TT §3 の上に有界な試験複体。
-/
instance leftSmallAcyclicComplex_isStrictlyLE :
    (leftSmallAcyclicComplex G hG M hM top ψ).IsStrictlyLE top := by
  change ((leftSmallAcyclicChain G hG M hM top ψ).extend
    (ComplexShape.embeddingUpIntLE top)).IsStrictlySupported (ComplexShape.embeddingUpIntLE top)
  infer_instance

/--
概要：整数部分複体の全項は生成対象だけから定まる固定対象の商。
方針：自然数方向の各項の全射を、零延長の成分同型へ合成する。
規約：元の整数複体や指定した射には上界が依存しない。
使われ方：Stacks 19.12.2、TT §3 の小さい複体代表族への所属。
-/
lemma leftSmallAcyclicComplex_term_cover (n : ℤ) :
    ∃ p : smallAcyclicUniformBound G ⟶ (leftSmallAcyclicComplex G hG M hM top ψ).X n, Epi p :=
  exists_epi_to_extended_term _ _ (smallAcyclicUniformBound G)
    (fun i => ⟨smallAcyclicChainCover G hG _ ψ _ i, inferInstance⟩) n

/--
概要：指定した生成対象からの射は構成した整数部分複体の対応する項を経由する。
方針：像への全射を延長の成分同型の逆へ合成し、包含の公式で検証する。
規約：次数は埋め込みの一の像。
使われ方：Stacks 19.12.2、TT §3 の非零な小さい部分複体の存在。
-/
lemma leftSmallAcyclicComplex_factor :
    ∃ p : G ⟶ (leftSmallAcyclicComplex G hG M hM top ψ).X
        ((ComplexShape.embeddingUpIntLE top).f 1),
      p ≫ (leftSmallAcyclicComplexInclusion G hG M hM top ψ).f
        ((ComplexShape.embeddingUpIntLE top).f 1) = ψ := by
  let L := leftSmallAcyclicChain G hG M hM top ψ
  let e := ComplexShape.embeddingUpIntLE top
  refine ⟨factorThruImage ψ ≫ (L.extendXIso e (i := 1) rfl).inv, ?_⟩
  change (factorThruImage ψ ≫ (L.extendXIso e (i := 1) rfl).inv) ≫
    descFromExtendedComplexComponent e (leftSmallAcyclicChainInclusion G hG M hM top ψ)
      (e.f 1) = ψ
  rw [descFromExtendedComplexComponent_eq e _ rfl]
  change (factorThruImage ψ ≫ (L.extendXIso e (i := 1) rfl).inv) ≫
    (L.extendXIso e (i := 1) rfl).hom ≫ image.ι ψ ≫ 𝟙 _ = ψ
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Category.comp_id, image.fac]

end SerrePositivity.KST.DerivedGeometry
