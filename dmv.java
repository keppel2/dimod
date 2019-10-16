import java.math.BigInteger;
import java.util.Hashtable;
import java.util.Stack;

public class dmv implements dimodTreeConstants, dimodVisitor
{
  private class Var
  {
    public int width;
    public int[] dims;
    private BigInteger[] data;
    public Var(int width, int[] dims)
    {
      int i;
      if (width == 0) {
        throw new Error("Zero width declaration.");
      }
      this.width = width;
      this.dims = dims;
      data = new BigInteger[Pi(dims.length)];
      for(i = 0; i < data.length; i++) {
        data[i] = new BigInteger("0");
      }
    }

    public int maxHexStringLength(int[] dims)
    {
      Validate(dims);
      return 1 + ((Pi(this.dims.length - dims.length) * width - 1) / 4);
    }

    private void Validate(int[] dimtest)
    {
      int i;
      if (dimtest.length > dims.length)
        throw new Error("Dimension count overflow.");
      for(i = 0; i < dimtest.length; i++)
      if(dimtest[i] > dims[dims.length - dimtest.length + i])
        throw new Error("Overflow in a dimension.");
    }

    private int Pi(int n)
    {
      int i,rt;
      rt= 1;
      for(i = 0; i < n; i++)
      {
        if(dims[i] < 1) {
          throw new Error("Dimension less than one.");
        }
        rt *= dims[i];
      }
      return rt;
    }

      public BigInteger getData(int[] dims)
    {
      int i,BeginS,EndS; BigInteger b=new BigInteger("0");
      BeginS=0;
      Validate(dims);
      for(i=0;i<dims.length;i++)
      {
        BeginS+=dims[i]*Pi(this.dims.length-dims.length+i);
      }
      EndS=BeginS+Pi(this.dims.length-dims.length);
      for(i=(EndS-1);i>=BeginS;i--)
      {
        b=b.shiftLeft(width);
        b=b.add(data[i]);
      }
      return b;
    }

    public void putData(int[] dims,BigInteger value)
    {
      int i,BeginS,EndS;
      if (value.signum()==-1)
        throw new Error("Negative assignment.");
      BeginS=0;
      Validate(dims);
      for(i=0;i<dims.length;i++)
      {
        BeginS+=dims[i]*Pi(this.dims.length-dims.length+i);
      }
      EndS=BeginS+Pi(this.dims.length-dims.length);
      for(i=BeginS;i<EndS;i++)
      {
        data[i]=value.mod(BigInteger.ONE.shiftLeft(width));
        value=value.shiftRight(width);
      }
      if (value.signum()!=0)
       throw new Error("Overflow on put");
    }
  }

  public static Hashtable symtab;
  public static Hashtable functab;
  public static Stack stack;
  public static Stack localvar;
  dmv ()
  {
    symtab = new Hashtable() ;
    functab = new Hashtable() ;
    stack = new Stack() ;
    localvar = new Stack();
  }

  public Object visit(SimpleNode node, Object data)
  {
    throw new Error("SimpleNode");
  }
  public Object visit(ASTExpressionList n, Object data)
  {
    BigInteger[] rt;
    int i, k = n.jjtGetNumChildren();
    rt=new BigInteger[k];
    for (i = 0; i < k; i++)
    {
      n.jjtGetChild(i).jjtAccept(this, data);
      rt[i]=popStack();
    }
    stack.push(rt);
    return data;
  }

  public Object visit(ASTCompilationUnit n, Object data)
  {
    int i, k = n.jjtGetNumChildren();
    BigInteger[] command=new BigInteger[dimod.command.length];
    localvar.push(new Hashtable());
    for (i=0; i < k; i++)
    {
      if(  ( (SimpleNode)n.jjtGetChild(i)).id==JJTFUNCTION)
      {
        if (functab.containsKey( (String) dimod.table.get(n.jjtGetChild(i) ) ) )
          throw new Error ("Function name taken.");
        functab.put( (String)dimod.table.get(n.jjtGetChild(i)),n.jjtGetChild(i));
      }
      else n.jjtGetChild(i).jjtAccept(this, data);
    }
    if(functab.isEmpty())
      return data;
    for(i=0;i<dimod.command.length;i++)
    {
      command[i]=new BigInteger(dimod.command[i],0x10);
    }
    stack.push(command);
    if(functab.containsKey("$main"))
      ((SimpleNode)functab.get("$main")).jjtAccept(this,data);
    else throw new Error ("$main not defined.");
    return data;
  }

  public Object visit(ASTFunction n, Object data)
  {
    BigInteger b;
    String name,s;
    int i,count,width;
    Var v;
    int k=n.jjtGetNumChildren();
    int[] dims=new int[0];
    int CurrentChild=0;
    BigInteger[] params=null;
    name=(String)dimod.table.get(n);
    count=((Integer)dimod.itable.get(n)).intValue();
    localvar.push(new Hashtable());
    n.jjtGetChild(CurrentChild).jjtAccept(this,data);
    width=bigIntegerToUInt(popStack());
    CurrentChild++;
    if( ((SimpleNode)n.jjtGetChild(CurrentChild)) .id==JJTEXPRESSIONLIST)
    {
      if(width==0)
        throw new Error ("Cannot make array with zero width.");
      n.jjtGetChild(CurrentChild).jjtAccept(this,data);
      CurrentChild++;
      dims=bigIntegerArrayToUInt((BigInteger[])stack.pop());
     }
    if (width>0)
      ((Hashtable)localvar.peek()).put("$",new Var(width,dims));
    params=(BigInteger[])stack.pop();
    if(params.length!=count)
      throw new Error ("Parameter count mismatch.");
    for(i=CurrentChild;i<(count+CurrentChild);i+=1)
    {
      n.jjtGetChild(i).jjtAccept(this,data);
      v=(Var) ((Hashtable)localvar.peek() ).get( dimod.table.get(n.jjtGetChild(i))) ;
      v.putData(new int[0],params[i-CurrentChild]);
      ((Hashtable)localvar.peek() ).put( (String) dimod.table.get(n.jjtGetChild(i)),v);
    }
    CurrentChild+=count;
    for(i=CurrentChild;i<k;i+=1)
      n.jjtGetChild(i).jjtAccept(this,data);
    if( ( (Hashtable)localvar.peek() ).containsKey("$"))
      stack.push(  ( (Var) ((Hashtable)localvar.peek()).get("$") ).getData(new int[0]) );
    else stack.push("Void");
    if(name.equals("$main"))
    if( ( (Hashtable)localvar.peek() ).containsKey("$"))
    {
      b=popStack();
      s=b.toString(0x10);
      System.out.println("Main returns "+s.toUpperCase());
    } else System.out.println("Main returns Void.");
    localvar.pop();
    return data;
  }

  public Object visit(ASTDeclaration n, Object data)
  {
    Hashtable current;
    String name;
    int width;
    int[] dims=new int[0];
    int i;
    BigInteger init=new BigInteger("0");
    Var v;
    int k=n.jjtGetNumChildren();
    name=(String)dimod.table.get(n);
    if(name.equals("$")) throw new Error("Cannot declare $.");
    if( ((SimpleNode)n.jjtGetParent()).id==JJTCOMPILATIONUNIT) current=symtab;
    else
      current=(Hashtable)localvar.peek();
    if(current.containsKey(name))
      throw new Error("Repeat symbol declaration.");
    n.jjtGetChild(0).jjtAccept(this,data);
    width=bigIntegerToUInt(popStack());
    for (i = 1; i < k; i++)
    {
      if(  ( (SimpleNode)n.jjtGetChild(i)).id==JJTEXPRESSIONLIST)
      {
        n.jjtGetChild(i).jjtAccept(this,data);
        dims=bigIntegerArrayToUInt((BigInteger[])stack.pop());
      }
      else
      {
        n.jjtGetChild(i).jjtAccept(this,data);
        init=popStack();
      }
    }
    v=new Var(width,dims);v.putData(new int[0],init);
    current.put(name,v);
    return data ;
  }

  public Object visit(ASTAssignment n, Object data)
  {
    BigInteger value;
    Var f2;
    String tname;
    int[] dims;
    Hashtable current;
    String name;
    tname=(String)dimod.table.get(n);
    n.jjtGetChild(1).jjtAccept(this, data);  // value left on stack
    value=popStack();
    n.jjtGetChild(0).jjtAccept(this, data);
    name=(String)stack.pop();
    if( ((Hashtable)localvar.peek()) .containsKey(name))
      current=(Hashtable)localvar.peek();
    else
      current=symtab;
    dims=(int[])stack.pop();
    f2=(Var)current.get(name);
    if(!tname.equals(":") )
      f2.putData( dims,doOp(f2.getData(dims),value,tname.substring(0,tname.length()-1)) );
    else f2.putData(dims,value);
    current.put(name,f2);
    stack.push(value);
    return data ;
  }

  public Object visit(ASTBinaryExpression n, Object data)
  {
   int i;
   int k;
    k = n.jjtGetNumChildren();
    for (i = 0; i < k; i++)
      n.jjtGetChild(i).jjtAccept(this, data);
    return data ;
  }

  public Object visit(ASTBinaryOperation n, Object data)
  {
    int f0;
    String name;
    BigInteger f=new BigInteger("0");
    name=(String)dimod.table.get(n);
    n.jjtGetChild(0).jjtAccept(this, data);
    BigInteger arg2 = popStack() ;
    BigInteger arg1 = popStack() ;
    f=doOp(arg1,arg2,name);
    stack.push(f);
    return data ;
  }

  public Object visit(ASTId n, Object data)
  {
    String name;
    int[] dims=new int[0];
    Var a;
    name=(String)dimod.table.get(n);
    Hashtable current;
    if( ( (Hashtable)localvar.peek() ).containsKey(name))
      current=(Hashtable)localvar.peek();
    else if(symtab.containsKey(name))
      current=symtab;
    else throw new Error("Symbol does not exist in expression.");
    a=(Var)current.get(name);
    if( (a.dims.length>0) && !dimod.itable.containsKey(n) )

    throw new Error("Brackets needed on id array.");

    if(n.jjtGetNumChildren()==1)
    {
      if(a.dims.length==0) throw new Error("Brackets on id non-array.");
      n.jjtGetChild(0).jjtAccept(this, data);
      dims=bigIntegerArrayToUInt((BigInteger[])stack.pop());
    }
    stack.push( a.getData(dims) );
    return data ;
  }

  public Object visit(ASTLValue n, Object data)
  {
    String name;
    int[] dims=new int[0];
    Var a;
    name=(String)dimod.table.get(n);
    Hashtable current;
    if( ( (Hashtable)localvar.peek() ).containsKey(name))
      current=(Hashtable)localvar.peek();
    else if(symtab.containsKey(name))
      current=symtab;
    else throw new Error("Symbol does not exist in l-value.");

    a=(Var)current.get(name);
    if( (a.dims.length>0) && !dimod.itable.containsKey(n) )
      throw new Error("Brackets needed on l-value array.");
    if(n.jjtGetNumChildren()==1)
    {
      if (a.dims.length==0)
        throw new Error("Brackets on l-value non-array.");
      n.jjtGetChild(0).jjtAccept(this, data);
      dims=bigIntegerArrayToUInt((BigInteger[])stack.pop());
    }
    stack.push(dims);
    stack.push(name) ;
    return data ;
  }

  public Object visit(ASTFunctionCall n, Object data)
  {
    String name;
    name=(String)dimod.table.get(n);
    if(!functab.containsKey(name))
      throw new Error("Function not defined.");
    int i;int k=n.jjtGetNumChildren();
    BigInteger[] params=new BigInteger[0];
    if(k==1)
      n.jjtGetChild(0).jjtAccept(this,data);
    else stack.push(params);
    ((SimpleNode)functab.get(name)).jjtAccept(this,data);
    return data;
  }

  public Object visit(ASTLiteral n, Object data)
  {
    String name;
    name=(String)dimod.table.get(n);
    stack.push(new BigInteger(name,0x10))  ;
    return data;
  }

  public Object visit(ASTNullStatement n, Object data)
  {
    return data;
  }

  public Object visit(ASTIfStatement n, Object data)
  {
    BigInteger b;
    n.jjtGetChild(0).jjtAccept(this, data);
    b=popStack();
    if( (b.signum()==-1) || ( b.compareTo(new BigInteger("1"))==1 ) )
      throw new Error ("0 or 1 expected for test expression.");
    if (b.signum()!=0)
      n.jjtGetChild(1).jjtAccept(this, data);
    else if (n.jjtGetNumChildren() == 3)
      n.jjtGetChild(2).jjtAccept(this, data);
    return data ;
  }

  public Object visit(ASTWhileStatement n, Object data)
  {
    BigInteger b;boolean stayin=true;
    do
    {
      n.jjtGetChild(0).jjtAccept(this, data);
      b=popStack();
      if( (b.signum()==-1) || ( b.compareTo(new BigInteger("1"))==1 ) )
        throw new Error ("0 or 1 expected for test expression.");
      if (b.signum()!=0)
        n.jjtGetChild(1).jjtAccept(this, data) ;
      else
        stayin=false;
    } while (stayin);
    return data ;
  }
  public Object visit(ASTRepeatStatement n, Object data)
  {
    BigInteger b;
    boolean stayin=true;
    do
    {
      n.jjtGetChild(0).jjtAccept(this, data);
      n.jjtGetChild(1).jjtAccept(this, data);
      b=popStack();
      if( (b.signum()==-1) || (b.compareTo(new BigInteger("1"))==1 ) )
        throw new Error ("0 or 1 expected for test expression.");
      if (b.signum()!=0)
        stayin=false;
    } while (stayin);
    return data;
  }

  public Object visit(ASTStringExpression n, Object data)
  {
    String name;
    name=(String)dimod.table.get(n);
    stack.push(name);
    return data;
  }

  public Object visit(ASTWriteStatement n, Object data)
  {
    String s;
    BigInteger b;
    int i, k = n.jjtGetNumChildren();
    for (i=0; i < k; i++)
    {
      n.jjtGetChild(i).jjtAccept(this, data);
      if(  ( (SimpleNode)n.jjtGetChild(i)).id!=JJTSTRINGEXPRESSION)
      {
        b=popStack();
        s=b.toString(0x10);
        System.out.print(s.toUpperCase());
      } else
      {
        s=(String)stack.pop();
        s=s.substring(1,s.length()-1);
        s=s.replaceAll("\\\\n","\n");
        System.out.print(s);
      }
    }
    return data ;
  }

  public Object visit(ASTWriteFillStatement n, Object data)
  {
    String s,name;
    BigInteger b;
    Hashtable current;
    int[] dims;
    Var v;
    int i, k = n.jjtGetNumChildren();
    for (i=0; i < k; i++)
    {
      n.jjtGetChild(i).jjtAccept(this, data);
      if(  ( (SimpleNode)n.jjtGetChild(i)).id!=JJTSTRINGEXPRESSION)
      {
        name=(String)stack.pop();
        if( ((Hashtable)localvar.peek()) .containsKey(name))
          current=(Hashtable)localvar.peek();
        else
          current=symtab;
        dims=(int[])stack.pop();
        v=(Var)current.get(name);
        b=v.getData(dims);
        s=b.toString(0x10);
        while(s.length()<v.maxHexStringLength(dims)) s="0"+s;
        System.out.print(s.toUpperCase());
      } else
      {
        s=(String)stack.pop();
        s=s.substring(1,s.length()-1);
        s=s.replaceAll("\\\\n","\n");
        System.out.print(s);
      }
    }
    return data ;
  }

  public Object visit(ASTCompoundStatement n, Object data)
  {
    int i; int k = n.jjtGetNumChildren();
    for (i = 0; i < k; i++)
      n.jjtGetChild(i).jjtAccept(this, data);
    return data;
  }

  public Object visit(ASTExpressionStatement n, Object data)
  {
    n.jjtGetChild(0).jjtAccept(this, data);
    stack.pop();
    return data;
  }

  private int bigIntegerToUInt(BigInteger a)
  {
    if(a.signum()==-1)
      throw new Error ("Negative BigInteger converted to int.");
    if(a.compareTo(new BigInteger("7fffffff",0x10))==1)
      throw new Error ("Oversize BigInteger converted to int.");
    return a.intValue();
  }

  private int[] bigIntegerArrayToUInt (BigInteger[] a)
  {
    int b;
    int[] rt=new int[a.length];
    for(b=0;b<a.length;b++)
    {
      if(a[b].signum()==-1)
        throw new Error ("Negative BigInteger converted to int.");
      if(a[b].compareTo(new BigInteger("7fffffff",0x10))==1)
        throw new Error ("Oversize BigInteger converted to int.");
      rt[a.length-1-b]=a[b].intValue();
    }
    return rt;
  }

  private BigInteger popStack ()
  {
    BigInteger rt;
    try
    {
      rt=(BigInteger)stack.pop();
    }
    catch (ClassCastException e) {throw new Error ("Attempted to use a void return.");}
    return rt;
  }

  private BigInteger doOp (BigInteger arg1, BigInteger arg2, String name)
  {
    BigInteger f=new BigInteger("0");
    if(name.equals("+"))
      f=arg1.add(arg2);
    else if(name.equals("-"))
      f=arg1.subtract(arg2);
    else if(name.equals("*"))
      f=arg1.multiply(arg2);
    else if(name.equals("/"))
      f=arg1.divide(arg2);
    else if(name.equals("**"))
      f=arg1.pow(arg2.intValue());
    else if ( (name.equals("<")) && (arg1.compareTo(arg2)==-1) )
      f=BigInteger.ONE;
    else if( (name.equals("=")) && (arg1.compareTo(arg2)==0) )
      f=BigInteger.ONE;
    else if( (name.equals("!=")) && (arg1.compareTo(arg2)!=0) )
      f=BigInteger.ONE;
    else if( (name.equals(">")) && (arg1.compareTo(arg2)==1) )
      f=BigInteger.ONE;
    else if ( (name.equals("<=")) && (arg1.compareTo(arg2)!=1) )
      f=BigInteger.ONE;
    else if ( (name.equals(">=")) && (arg1.compareTo(arg2)!=-1) )
      f=BigInteger.ONE;
    else if( (arg1.signum()==-1) || (arg2.signum()==-1) )
      throw new Error("An operand is negative.");
    else if(name.equals("/+") || name.equals("%"))
      f=arg1.mod(arg2);
    else if(name.equals("~+") || name.equals("&"))
      f=arg1.and(arg2);
    else if(name.equals("|"))
      f=arg1.or(arg2);
    else if(name.equals("~|") || name.equals("^"))
      f=arg1.xor(arg2);
    else if(name.equals("<<"))
      f = arg1.shiftLeft(bigIntegerToUInt(arg2));
    else if(name.equals(">>"))
      f = arg1.shiftRight(bigIntegerToUInt(arg2));
  return f;
  }
}
