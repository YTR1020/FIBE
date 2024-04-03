import it.unisa.dia.gas.jpbc.Element;
import it.unisa.dia.gas.jpbc.Field;
import it.unisa.dia.gas.jpbc.Pairing;
import it.unisa.dia.gas.plaf.jpbc.pairing.PairingFactory;

import java.io.FileInputStream;
import java.io.FileOutputStream;
import java.io.IOException;
import java.security.NoSuchAlgorithmException;
import java.util.Arrays;
import java.util.Base64;
import java.util.Properties;

import java.io.BufferedReader;
import java.io.BufferedWriter;
import java.io.FileReader;
import java.io.FileWriter;

import java.math.BigInteger;
import java.nio.charset.StandardCharsets;
import java.security.MessageDigest;

//import org.apache.commons.codec.binary.Hex;




public class FIBE {

    public static void setup(String pairingParametersFileName, int U, int d, String pkFileName, String mskFileName) {
        //输入为 < 相关初始化参数文件名，属性全集U（整数），系统门限d（整数），公钥集文件名，主密钥集文件名 >
        Pairing bp = PairingFactory.getPairing(pairingParametersFileName);  //从文件导入椭圆曲线参数，生成Pairing实例
        Element g = bp.getG1().newRandomElement().getImmutable();  //基于基本参数，从G1乘法循环群中随机选取Element整数生成元g（阶数）

        Properties mskProp = new Properties();  //新建Properties类以便生成对应主密钥msk封装文件
        Properties pkProp = new Properties();  //新建Properties类以便生成对应公钥pk封装文件
        //属性表示为1，2，3，...，U
        //对每个属性i，选取一个随机数ti作为该属性对应的主密钥，并计算相应公钥g^ti
        for (int i = 1; i <= U; i++){
            Element t = bp.getZr().newRandomElement().getImmutable();  //Element整数ti需要从加法循环群Zp中随机选取
            Element T = g.powZn(t).getImmutable();  //Element整数Ti=g^ti
            mskProp.setProperty("t"+i, Base64.getEncoder().withoutPadding().encodeToString(t.toBytes()));
            pkProp.setProperty("T"+i, Base64.getEncoder().withoutPadding().encodeToString(T.toBytes()));
            //将所得ti、Ti转换为字符串形式并进行Base64编码，并存入对应主密钥、公钥文件中
        }
        //另外选取一个随机数y，计算e(g,g)^y
        Element y = bp.getZr().newRandomElement().getImmutable();  //Element整数y需要从加法循环群Zp中随机选取
        Element egg_y = bp.pairing(g, g).powZn(y).getImmutable();  //基于椭圆曲线基本参数计算Y=egg_y=e(g,g)^y
        mskProp.setProperty("y", Base64.getEncoder().withoutPadding().encodeToString(y.toBytes()));
        pkProp.setProperty("egg_y", Base64.getEncoder().withoutPadding().encodeToString(egg_y.toBytes()));
        pkProp.setProperty("g", Base64.getEncoder().withoutPadding().encodeToString(g.toBytes()));
        //将所得y、egg_y、g转换为字符串形式并进行Base64编码，并存入对应主密钥、公钥、公钥文件中
        //注意区分数据类型。上面写的数据类型群元素，因此使用了Base64编码。
        //d在实际应用中定义为一个int类型，直接用Integer.toString方法转字符串
        pkProp.setProperty("d", Integer.toString(d));

        storePropToFile(mskProp, mskFileName);  //封装进对应文件
        storePropToFile(pkProp, pkFileName);  //封装进对应文件
        //输出：系统主密钥文件 msk = < t1, t2, ..., t|U|, y >，公钥文件 pk = < T1, T2, ..., T|U|, Y, g, d >
    }

    public static void keygen(String pairingParametersFileName, int[] userAttList, String pkFileName, String mskFileName, String skFileName) throws NoSuchAlgorithmException {
        //输入为 < 相关初始化参数文件名，用户整数属性集，公钥文件名，主密钥文件名，私钥文件名 >
        Pairing bp = PairingFactory.getPairing(pairingParametersFileName);  //从文件导入椭圆曲线参数，生成Pairing实例

        Properties pkProp = loadPropFromFile(pkFileName);  //从对应公钥pk封装文件载入公钥Properties实例
        String gString = pkProp.getProperty("g");  //从对应公钥pk文件中获取生成元g
        Element g = bp.getG1().newElementFromBytes(Base64.getDecoder().decode(gString)).getImmutable();
        //将Base64编码后的字符串g解码转换成Element类整数
        String dString = pkProp.getProperty("d");  //从对应公钥pk文件中获取系统门限值d
        int d = Integer.parseInt(dString);
        //将字符串d解码转换成int类整数

        Properties mskProp = loadPropFromFile(mskFileName);  //从对应主密钥msk封装文件载入主密钥Properties实例
        String yString = mskProp.getProperty("y");  //从对应主密钥msk文件中获取随机数密钥y值
        Element y = bp.getZr().newElementFromBytes(Base64.getDecoder().decode(yString)).getImmutable();
        //将Base64编码后的字符串y解码转换成Element类整数

        //d-1次多项式表示为q(x)=coef[0] + coef[1]*x^1 + coef[2]*x^2 + coef[d-1]*x^(d-1)
        //多项式的系数的数据类型为Zr Element，从而使得后续相关计算全部在Zr群上进行
        //通过随机选取coef参数，来构造d-1次多项式q(x)。约束条件为q(0)=y。
        Element[] coef = new Element[d];  //多项式的系数coef个数为d个
        coef[0] = y;  //约束条件即赋值q(0)=a0=coef[0]=y
        for (int i = 1; i < d; i++){
            coef[i] = bp.getZr().newRandomElement().getImmutable();
            //在Zp群上进行随机选取多项式的系数coef
        }

        Properties skProp = new Properties();  //新建Properties类以便生成对应私钥sk封装文件
        //计算用户属性中每个属性对应的私钥Di=g^(q(i)/ti)，q(i)是多项式在该属性i位置的值，ti是属性对应的主密钥
        for (int att : userAttList) {
            String tString = mskProp.getProperty("t"+att);  //从对应主密钥msk文件中获取对应ti的字符串
            Element t = bp.getZr().newElementFromBytes(Base64.getDecoder().decode(tString)).getImmutable();
            //将Base64编码后的字符串t解码转换成Element类整数
            Element q = qx(bp.getZr().newElement(att), coef, bp.getZr()).getImmutable();
            //计算Element类整数值q(i)=q(att)=coef[0] + coef[1]*att^1 + coef[2]*att^2 + coef[d-1]*att^(d-1)
            //编写了函数qx来计算由coef为系数确定的多项式qx在点x处的值，注意多项式计算在群Zr上进行
            Element D = g.powZn(q.div(t)).getImmutable();
            //计算Element类整数值Di=g^(q(i)/ti)

            skProp.setProperty("D"+att, Base64.getEncoder().withoutPadding().encodeToString(D.toBytes()));
            //将所得Di转换为字符串形式并进行Base64编码，并存入对应私钥文件中
        }
        //将用户属性列表userAttList也添加在私钥中
        skProp.setProperty("userAttList", Arrays.toString(userAttList));
        storePropToFile(skProp, skFileName);  //封装进对应文件
        //输出：私钥文件 sk = < {Di}(i∈userAttList), userAttList >
    }

    public static void encrypt(String pairingParametersFileName, Element message, int[] messageAttList, String pkFileName, String ctFileName) {
        //输入为 < 相关初始化参数文件名，Element类明文信息（GT上一点），明文属性集，公钥文件名，密文文件名 >
        Pairing bp = PairingFactory.getPairing(pairingParametersFileName);  //从文件导入椭圆曲线参数，生成Pairing实例

        Properties pkProp = loadPropFromFile(pkFileName);  //从对应公钥pk封装文件载入公钥Properties实例
        String eggString = pkProp.getProperty("egg_y");  //从对应公钥pk文件中获取公钥egg_y=Y=e(g,g)^y
        Element egg_y = bp.getGT().newElementFromBytes(Base64.getDecoder().decode(eggString)).getImmutable();
        //将Base64编码后的字符串egg_y解码转换成Element类整数

        //计算密文组件 EP=Me(g,g)^(ys)
        Element s = bp.getZr().newRandomElement().getImmutable();
        //选取随机Element类整数s∈Zp
        Element EP = message.duplicate().mul(egg_y.powZn(s)).getImmutable();
        //计算Element类整数EP=M(Y^s)=Me(g,g)^(ys)（M点进行双线性映射得到整数）

        Properties ctProp = new Properties();  //新建Properties类以便生成对应密文ct封装文件
        //针对每个明文属性，计算密文组件 Ei=Ti^s
        for (int att : messageAttList) {
            String TString = pkProp.getProperty("T"+att);  //从对应公钥pk文件中获取对应Ti的字符串
            Element T = bp.getG1().newElementFromBytes(Base64.getDecoder().decode(TString)).getImmutable();
            //将Base64编码后的字符串Ti解码转换成Element类整数
            Element E = T.powZn(s).getImmutable();
            //针对每个明文属性，计算密文组件Element类整数 Ei=Ti^s

            ctProp.setProperty("E"+att, Base64.getEncoder().withoutPadding().encodeToString(E.toBytes()));
            //将所得密文组件Ei转换为字符串形式并进行Base64编码，并存入对应密文文件中
        }
        ctProp.setProperty("EP", Base64.getEncoder().withoutPadding().encodeToString(EP.toBytes()));
        //将Element类整数EP=M(Y^s)=Me(g,g)^(ys)也转换为字符串形式并进行Base64编码，并存入对应密文文件中
        //密文属性列表messageAttList也添加至密文文件中
        ctProp.setProperty("messageAttList", Arrays.toString(messageAttList));
        storePropToFile(ctProp, ctFileName);  //封装进对应文件
        //输出：密文文件 ct = < E', {Ei}(i∈messageAttList) , EP, messageAttList >
    }

    public static Element decrypt(String pairingParametersFileName, String pkFileName, String ctFileName, String skFileName) {
        //输入为 < 相关初始化参数文件名，公钥文件名，密文文件名，私钥文件名 >
        Pairing bp = PairingFactory.getPairing(pairingParametersFileName);  //从文件导入椭圆曲线参数，生成Pairing实例

        Properties pkProp = loadPropFromFile(pkFileName);  //从对应公钥pk封装文件载入公钥Properties实例
        String dString = pkProp.getProperty("d");  //从对应公钥pk文件中获取公钥系统门限值d
        int d = Integer.parseInt(dString);
        //将字符串d解码转换成int类整数

        Properties ctProp = loadPropFromFile(ctFileName);  //从对应密文ct封装文件载入密文Properties实例
        String messageAttListString = ctProp.getProperty("messageAttList");  //从对应密文ct文件中获取明文属性列表
        //恢复明文消息的属性列表 int[]类型
        int[] messageAttList = Arrays.stream(messageAttListString.substring(1, messageAttListString.length()-1).split(",")).map(String::trim).mapToInt(Integer::parseInt).toArray();

        Properties skProp = loadPropFromFile(skFileName);  //从对应私钥sk封装文件载入私钥Properties实例
        String userAttListString = skProp.getProperty("userAttList");  //从对应私钥sk文件中获取用户属性列表
        //恢复用户属性列表 int[]类型
        int[] userAttList = Arrays.stream(userAttListString.substring(1, userAttListString.length()-1).split(",")).map(String::trim).mapToInt(Integer::parseInt).toArray();

        //判断两个列表重合个数是否小于d
        int[] intersectionAttList = intersection(messageAttList, userAttList);  //编写了求两个数组的交集的函数intersection
        System.out.println("重合属性列表：" + Arrays.toString(intersectionAttList));
        System.out.println("重合属性个数为：" + intersectionAttList.length);
        if (intersectionAttList.length < d) {
            System.out.println("不满足解密门限，无法解密！");
            return null;
        }
        //从两个列表中的重合项中取前d项，构成解密属性列表
        int[] decAttList = Arrays.copyOfRange(intersectionAttList, 0, d);
        System.out.println("解密所用属性列表：" + Arrays.toString(decAttList));

        Element denominator = bp.getGT().newOneElement().getImmutable();
        //从GT中生成一个Element实例，作为Pi=e(Di,Ei)^delta(0)的连乘结果denominator
        //针对解密属性列表中的每个属性，计算Pie(Di,Ei)^delta(0)，并将结果连乘
        for (int att : decAttList){
            String EString = ctProp.getProperty("E"+att);  //从对应密文ct文件中获取密文组件Ei
            Element E = bp.getG1().newElementFromBytes(Base64.getDecoder().decode(EString)).getImmutable();
            //将Base64编码后的字符串Ei解码转换成Element类整数
            String DString = skProp.getProperty("D"+att);  //从对应私钥sk文件中获取用户每个属性对应的私钥Di
            Element D = bp.getG1().newElementFromBytes(Base64.getDecoder().decode(DString)).getImmutable();
            //将Base64编码后的字符串Di解码转换成Element类整数

            //计算属性对应的拉格朗日因子，作为指数。目标值x为0。
            Element delta = lagrange(att, decAttList, 0, bp.getZr()).getImmutable();
            //编写了拉格朗日因子计算lagrange函数
            denominator = denominator.mul(bp.pairing(E,D).powZn(delta));
            //计算Pi=e(Di,Ei)^deltai(0)=e(g,g)^sq(i)deltai(0)，并将结果连乘
            //实际上得到denominator=e(g,g)^(s·(求和q(i)deltai(0)))===e(g,g)^sy
        }

        String EPString = ctProp.getProperty("EP");  //从对应密文ct文件中获取EP=M(Y^s)=Me(g,g)^(ys)
        Element EP = bp.getGT().newElementFromBytes(Base64.getDecoder().decode(EPString)).getImmutable();
        //将Base64编码后的字符串Di解码转换成Element类整数
        //恢复M=EP/denominator=Me(g,g)^(ys)/e(g,g)^sy=M
        Element res = EP.div(denominator);
        return res;
        //输出返回为解密后的M（点）
    }

    //计算由coef为系数确定的多项式qx在点x处的值，注意多项式计算在群Zr上进行
    public static Element qx(Element x, Element[] coef, Field Zr){
        Element res = coef[0];
        for (int i = 1; i < coef.length; i++){
            Element exp = Zr.newElement(i).getImmutable();
            //x一定要使用duplicate复制使用，因为x在每一次循环中都要使用，如果不加duplicte，x的值会发生变化
            res = res.add(coef[i].mul(x.duplicate().powZn(exp)));
        }
        return res;
    }

    //求两个数组的交集
    public static int[] intersection(int[] nums1, int[] nums2) {
        Arrays.sort(nums1);
        Arrays.sort(nums2);
        int length1 = nums1.length, length2 = nums2.length;
        int[] intersection = new int[length1 + length2];
        int index = 0, index1 = 0, index2 = 0;
        while (index1 < length1 && index2 < length2) {
            int num1 = nums1[index1], num2 = nums2[index2];
            if (num1 == num2) {
                // 保证加入元素的唯一性
                if (index == 0 || num1 != intersection[index - 1]) {
                    intersection[index++] = num1;
                }
                index1++;
                index2++;
            } else if (num1 < num2) {
                index1++;
            } else {
                index2++;
            }
        }
        return Arrays.copyOfRange(intersection, 0, index);
    }

    //拉格朗日因子计算 i是集合S中的某个元素，x是目标点的值
    public static Element lagrange(int i, int[] S, int x, Field Zr) {
        Element res = Zr.newOneElement().getImmutable();
        Element iElement = Zr.newElement(i).getImmutable();
        Element xElement = Zr.newElement(x).getImmutable();
        for (int j : S) {
            if (i != j) {
                //注意：在循环中重复使用的项一定要用duplicate复制出来使用
                //这儿xElement和iElement重复使用，但因为前面已经getImmutable所以可以不用duplicate
                Element numerator = xElement.sub(Zr.newElement(j));
                Element denominator = iElement.sub(Zr.newElement(j));
                res = res.mul(numerator.div(denominator));
            }
        }
        return res;
    }

    public static void storePropToFile(Properties prop, String fileName){
        try(FileOutputStream out = new FileOutputStream(fileName)){
            prop.store(out, null);
        }
        catch (IOException e) {
            e.printStackTrace();
            System.out.println(fileName + " save failed!");
            System.exit(-1);
        }
    }

    public static Properties loadPropFromFile(String fileName) {
        Properties prop = new Properties();
        try (FileInputStream in = new FileInputStream(fileName)){
            prop.load(in);
        }
        catch (IOException e){
            e.printStackTrace();
            System.out.println(fileName + " load failed!");
            System.exit(-1);
        }
        return prop;
    }

    // 从文件中读取明文字符串消息
    private static String readPlaintextFromFile(String fileName) {
        StringBuilder plaintext = new StringBuilder();
        try (BufferedReader reader = new BufferedReader(new FileReader(fileName))) {
            String line;
            while ((line = reader.readLine()) != null) {
                plaintext.append(line);
            }
        } catch (IOException e) {
            e.printStackTrace();
        }
        return plaintext.toString();
    }

    // 将明文字符串消息哈希为GT群上的点Element类
    private static Element hashToElement(String plaintext, String pairingParametersFileName) {
        try {
            MessageDigest digest = MessageDigest.getInstance("SHA-256");
            byte[] hashBytes = digest.digest(plaintext.getBytes(StandardCharsets.UTF_8));
            BigInteger hashInt = new BigInteger(1, hashBytes);
            return PairingFactory.getPairing(pairingParametersFileName).getGT().newElementFromHash(hashInt.toByteArray(), 0, hashInt.toByteArray().length);
        } catch (NoSuchAlgorithmException e) {
            e.printStackTrace();
        }
        return null;
    }



    public static void main(String[] args) throws Exception {
        int U = 20;
        int d = 5;
        System.out.println("系统解密门限为：" + d);

        int[] userAttList = {1, 5, 3, 6, 10, 11};
        int[] messageAttList = {1,  3,  5,  7, 9, 10, 11};

        String dir = "data/";
        String pairingParametersFileName = "a.properties";
        String pkFileName = dir + "pk.properties";
        String mskFileName = dir + "msk.properties";
        String skFileName = dir + "sk.properties";
        String ctFileName = dir + "ct.properties";

        String inputFileName = dir + "input.txt"; // 输入文件名


        // 读取明文字符串消息
        String plaintext = readPlaintextFromFile(inputFileName);
        System.out.println("明文消息: " + plaintext);

        // 将明文字符串消息哈希为GT群上的点Element类
        Element M = hashToElement(plaintext,pairingParametersFileName);

        // 打印哈希后的Element
        System.out.println("哈希后的明文消息: " + M);




        setup(pairingParametersFileName, U, d, pkFileName, mskFileName);

        keygen(pairingParametersFileName, userAttList, pkFileName, mskFileName, skFileName);

        System.out.println("加密密钥文件:" + pkFileName);

        //Element message = PairingFactory.getPairing(pairingParametersFileName).getGT().newRandomElement().getImmutable();

        //System.out.println("明文消息:" + message);
        //encrypt(pairingParametersFileName, message, messageAttList, pkFileName, ctFileName);
        encrypt(pairingParametersFileName, M, messageAttList, pkFileName, ctFileName);

        Element res = decrypt(pairingParametersFileName, pkFileName, ctFileName, skFileName);
        System.out.println("解密结果:" + res);
        if (M.isEqual(res)) {
            System.out.println("成功解密！");
        }

        //if (message.isEqual(res)) {
          //  System.out.println("成功解密！");
        //}


    }

}
